(* driver.ml
   Runs the EXTRACTED Coq core (Peaks.peaks + GridEncode.grid_encode) on a
   speckle image, writes the peaks list and grid encoding to JSON, and
   reproduces the per-image statistical analysis from peaks_processing.py so
   results can be diffed against the full C/Python pipeline.

   Input formats (auto-detected): BMP (8/24/32-bpp, BI_RGB) or the original
   plain-text "<w> <h>\n w*h ints, row-major".

   Statistics emitted (mirroring OPUF_Algorithm_Peaks_Processing, default
   settings: threshold=0, adjacency='all', bounding_box=default):

     <stats_dir>/speckle_count/<stem>-speckle_count.txt
         single int = # in-box speckles with weight > threshold
         (== get_speckles default-variant retCount)

     <stats_dir>/speckle_counts/<stem>-speckle_counts.txt
         lines "i,c" for i=0..20000, c = # in-box speckles with weight > i
         (== get_speckles default-variant count_dict, max_count=20000)

     <stats_dir>/simple_speckle_counts/<stem>-simple_speckle_counts.txt
         lines "t,c" for t=0..254, c = # of 8/4-connected components of
         {pixel : intensity > t} whose rounded centroid is in the box
         (== get_speckles GS_SIMPLE retCount, max_count=0)

   NOT reproduced: run_speckle_test / _speckle_count_test (default False; and
   as written it calls _get_peaks_len(tile) with a missing `threshold`
   argument, so it raises before doing anything).  The cross-image averages
   (_combine_speckle_count*, *.csv) are pure post-processing over the per-image
   files above and identical inputs give identical averages; run the unchanged
   Python combine step, or aggregate the per-image files directly.
*)

open Speckle_core

let pixel_area  = 20.0
let density     = 0.5
let threshold   = 0            (* peak weight threshold *)
let all_adjacent = true        (* adjacency = 'all'      *)
let max_count   = 20000        (* speckle_counts dict range (C max_count) *)

(* ---- array-backed gimage: in-bounds -> arr.(y*w+x), else 0 -------------- *)
let make_image w h (arr : int array) : gimage =
  { gw = w; gh = h;
    gpix = (fun x y ->
      if x >= 0 && x < w && y >= 0 && y < h
      then Array.unsafe_get arr (y * w + x) else 0) }

(* ---- little-endian readers over a Bytes.t -------------------------------- *)
let u16 b o = (Char.code (Bytes.get b o)) lor (Char.code (Bytes.get b (o+1)) lsl 8)
let u32 b o =
  (Char.code (Bytes.get b o))
  lor (Char.code (Bytes.get b (o+1)) lsl 8)
  lor (Char.code (Bytes.get b (o+2)) lsl 16)
  lor (Char.code (Bytes.get b (o+3)) lsl 24)
let i32 b o = let v = u32 b o in if v >= 0x80000000 then v - (1 lsl 32) else v

let read_all path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let b = Bytes.create n in
  really_input ic b 0 n; close_in ic; b

(* ---- BMP loader: returns (w,h,arr) with row 0 = top, values 0..255 ------ *)
let read_bmp path =
  let b = read_all path in
  if Bytes.length b < 54 || Bytes.get b 0 <> 'B' || Bytes.get b 1 <> 'M' then
    failwith "not a BMP file";
  let off  = u32 b 10 in
  let w    = i32 b 18 in
  let h_raw= i32 b 22 in
  let bpp  = u16 b 28 in
  let comp = u32 b 30 in
  if comp <> 0 then failwith "unsupported BMP compression (need BI_RGB)";
  let top_down = h_raw < 0 in
  let h = abs h_raw in
  let bytes_pp = bpp / 8 in
  if bpp <> 8 && bpp <> 24 && bpp <> 32 then
    failwith (Printf.sprintf "unsupported BMP bit depth: %d" bpp);
  let row_size = ((w * bytes_pp + 3) / 4) * 4 in
  let arr = Array.make (w * h) 0 in
  for y = 0 to h - 1 do
    let src_row = if top_down then y else h - 1 - y in
    let base = off + src_row * row_size in
    for x = 0 to w - 1 do
      let v =
        if bpp = 8 then Char.code (Bytes.get b (base + x))
        else begin
          let p = base + x * bytes_pp in
          let bl = Char.code (Bytes.get b p) in
          let gr = Char.code (Bytes.get b (p+1)) in
          let rd = Char.code (Bytes.get b (p+2)) in
          if rd = gr && gr = bl then rd
          else (299 * rd + 587 * gr + 114 * bl) / 1000
        end
      in
      arr.(y * w + x) <- v
    done
  done;
  (w, h, arr)

(* ---- original plain-text loader -> (w,h,arr) ---------------------------- *)
let read_text path =
  let ic = open_in path in
  let first = input_line ic in
  let w, h = Scanf.sscanf first " %d %d" (fun a b -> (a, b)) in
  let n = w * h in
  let buf = Buffer.create 4096 in
  (try while true do Buffer.add_channel buf ic 65536 done with End_of_file -> ());
  close_in ic;
  let s = Buffer.contents buf in
  let arr = Array.make n 0 in
  let j = ref 0 and k = ref 0 and len = String.length s in
  while !k < len && !j < n do
    while !k < len && (s.[!k] < '0' || s.[!k] > '9') do incr k done;
    if !k < len then begin
      let v = ref 0 in
      while !k < len && s.[!k] >= '0' && s.[!k] <= '9' do
        v := !v*10 + (Char.code s.[!k] - 48); incr k done;
      arr.(!j) <- !v; incr j
    end
  done;
  assert (!j = n);
  (w, h, arr)

let read_image path =
  let is_bmp_ext = Filename.check_suffix (String.lowercase_ascii path) ".bmp" in
  let magic_bm =
    try let ic = open_in_bin path in
        let ok = (try input_char ic = 'B' && input_char ic = 'M'
                  with End_of_file -> false) in
        close_in ic; ok
    with _ -> false in
  if is_bmp_ext || magic_bm then read_bmp path else read_text path

(* basename with the Python ".split('.bmp')[0]" behaviour *)
let stem_of path =
  let b = Filename.basename path in
  match String.index_opt b '.' with
  | _ ->
    (* mimic str.split('.bmp')[0]: prefix before first ".bmp", else whole base *)
    let needle = ".bmp" in
    let nl = String.length needle and bl = String.length b in
    let rec find i =
      if i + nl > bl then None
      else if String.sub b i nl = needle then Some i else find (i+1) in
    (match find 0 with Some i -> String.sub b 0 i | None -> b)

let mkdir_p d = (try Sys.mkdir d 0o755 with Sys_error _ -> ())  (* ignore "already exists" *)

(* C round(): round half away from zero (centroids here are non-negative) *)
let iround x = int_of_float (Float.round x)

(* offset arrays, byte-for-byte as speckle.c (cardinal[] / all[]) *)
let all_offsets      = [| (0,1);(1,1);(1,0);(1,-1);(0,-1);(-1,-1);(-1,0);(-1,1) |]
let cardinal_offsets = [| (0,1);(1,0);(0,-1);(-1,0) |]

(* ===== GS_SIMPLE: connected-component count of {intensity > t} ===========
   Faithful to speckle.c lines 280-382: 8/4-connected flood over pixels with
   intensity > t; a component is counted iff its rounded centroid lies in the
   bounding box.  `visited` carries a per-threshold run-id so it never has to
   be cleared between thresholds. *)
let simple_count data w h offs (xmin,xmax,ymin,ymax) t visited run stack =
  let n = w*h in
  let count = ref 0 in
  let no = Array.length offs in
  (* C scans x outer, y inner; order is irrelevant to the component set *)
  for x = 0 to w-1 do
    for y = 0 to h-1 do
      let s = y*w + x in
      if Array.unsafe_get data s > t && Array.unsafe_get visited s <> run then begin
        (* flood this component *)
        let sp = ref 0 in
        Array.unsafe_set stack 0 s; sp := 1;
        Array.unsafe_set visited s run;
        let xs = ref 0 and ys = ref 0 and cnt = ref 0 in
        while !sp > 0 do
          decr sp;
          let p = Array.unsafe_get stack !sp in
          let px = p mod w and py = p / w in
          xs := !xs + px; ys := !ys + py; incr cnt;
          for o = 0 to no-1 do
            let (dx,dy) = Array.unsafe_get offs o in
            let nx = px+dx and ny = py+dy in
            if nx>=0 && nx<w && ny>=0 && ny<h then begin
              let np = ny*w+nx in
              if Array.unsafe_get data np > t
                 && Array.unsafe_get visited np <> run then begin
                Array.unsafe_set visited np run;
                Array.unsafe_set stack !sp np; incr sp
              end
            end
          done
        done;
        ignore n;
        let cx = iround (float !xs /. float !cnt) in
        let cy = iround (float !ys /. float !cnt) in
        if xmin<=cx && cx<=xmax && ymin<=cy && cy<=ymax then incr count
      end
    done
  done;
  !count

let () =
  Gc.set { (Gc.get ()) with
           Gc.minor_heap_size = 64 * 1024 * 1024 / 8;
           Gc.space_overhead  = 400 };
  let in_path  = Sys.argv.(1) in
  let out_path = Sys.argv.(2) in
  (* stats base dir: argv.(3) if given, else the directory of out_path *)
  let stats_dir =
    if Array.length Sys.argv > 3 then Sys.argv.(3)
    else (let d = Filename.dirname out_path in if d = "" then "." else d) in
  let (w, h, data) = read_image in_path in
  let img = make_image w h data in
  let (xmin,xmax,ymin,ymax) = (1, w-2, 1, h-2) in
  let stem = stem_of in_path in

  (* --- ONE expensive peaks() call at threshold 0 = full in-box speckle set.
         The thresholded set used for the grid is just a cheap filter of it. *)
  let ps_all = peaks img 0 all_adjacent xmin xmax ymin ymax in
  let ps_grid = List.filter (fun (_,wt) -> wt > threshold) ps_all in

  (* ---------- statistic 1 & 2: weight-based counts (default variant) ------ *)
  let weights = List.rev_map snd ps_all in
  (* hist.(min w (max_count+1)) of in-box speckle weights *)
  let hist = Array.make (max_count + 2) 0 in
  let total = ref 0 in
  List.iter (fun wt ->
      incr total;
      let idx = if wt > max_count then max_count+1 else wt in
      hist.(idx) <- hist.(idx) + 1) weights;
  (* count_dict.(i) = # weights > i  = total - sum_{k<=i} hist.(k) *)
  let count_dict = Array.make (max_count + 1) 0 in
  let running = ref !total in
  for i = 0 to max_count do
    running := !running - hist.(i);   (* subtract # with weight == i *)
    count_dict.(i) <- !running        (* # with weight > i *)
  done;
  let speckle_count = count_dict.(threshold) in  (* # weight > threshold *)

  mkdir_p stats_dir;
  let d_single = Filename.concat stats_dir "speckle_count" in
  let d_counts = Filename.concat stats_dir "speckle_counts" in
  let d_simple = Filename.concat stats_dir "simple_speckle_counts" in
  mkdir_p d_single; mkdir_p d_counts; mkdir_p d_simple;

  (* speckle_count/<stem>-speckle_count.txt : single int (no newline, as C) *)
  let oc = open_out (Filename.concat d_single (stem ^ "-speckle_count.txt")) in
  Printf.fprintf oc "%d" speckle_count; close_out oc;

  (* speckle_counts/<stem>-speckle_counts.txt : "i,count_dict[i]" i=0..max *)
  let oc = open_out (Filename.concat d_counts (stem ^ "-speckle_counts.txt")) in
  for i = 0 to max_count do Printf.fprintf oc "%d,%d\n" i count_dict.(i) done;
  close_out oc;

  (* ---------- statistic 3: simple variant over thresholds 0..254 ---------- *)
  let offs = if all_adjacent then all_offsets else cardinal_offsets in
  let visited = Array.make (w*h) 0 in
  let stack = Array.make (w*h) 0 in
  let oc = open_out (Filename.concat d_simple (stem ^ "-simple_speckle_counts.txt")) in
  for t = 0 to 254 do
    let c = simple_count data w h offs (xmin,xmax,ymin,ymax) t visited (t+1) stack in
    Printf.fprintf oc "%d,%d\n" t c
  done;
  close_out oc;

  (* ---------- grid encoding + JSON (unchanged comparison surface) --------- *)
  let ps_sorted = List.sort (fun ((x1,y1),_) ((x2,y2),_) ->
      if x1<>x2 then compare x1 x2 else compare y1 y2) ps_grid in
  let pm = Array.make (w*h) 0 in
  List.iter (fun ((x,y),wt) -> if y>=0 && y<h && x>=0 && x<w then pm.(y*w+x) <- wt) ps_sorted;
  let peakmap = make_image w h pm in
  let bits = grid_encode GHex peakmap img pixel_area density in
  let oc = open_out out_path in
  Printf.fprintf oc "{\n";
  Printf.fprintf oc "  \"w\": %d, \"h\": %d,\n" w h;
  Printf.fprintf oc "  \"speckle_count\": %d,\n" speckle_count;
  Printf.fprintf oc "  \"peaks\": [";
  List.iteri (fun i ((x,y),wt) ->
      if i>0 then Printf.fprintf oc ", ";
      Printf.fprintf oc "[%d, %d, %d]" x y wt) ps_sorted;
  Printf.fprintf oc "],\n";
  Printf.fprintf oc "  \"bits\": [";
  List.iteri (fun i b ->
      if i>0 then Printf.fprintf oc ", ";
      Printf.fprintf oc "%d" (if b then 1 else 0)) bits;
  Printf.fprintf oc "]\n}\n";
  close_out oc;
  Printf.printf "%s -> %d peaks (speckle_count=%d), %d bits | stats in %s/{speckle_count,speckle_counts,simple_speckle_counts}\n"
    (Filename.basename in_path) (List.length ps_sorted) speckle_count
    (List.length bits) stats_dir
