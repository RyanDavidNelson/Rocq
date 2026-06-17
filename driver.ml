(* driver.ml
   Runs the EXTRACTED Coq core (Peaks.peaks + GridEncode.grid_encode) on a
   speckle image and writes the peaks list and grid encoding to JSON.

   Input formats (auto-detected):
     * BMP  : files beginning with the "BM" magic (or a .bmp extension).
              Parsed as the Python pipeline treats them
              (core.py `_img_to_numpy`: np.asarray(Image.open(path),uint8)),
              i.e. an 8-bit grayscale bitmap; rows are returned top-first.
              24/32-bpp BMPs are reduced to luma as a best-effort.
     * text : the original plain-text format -
                line 1:  "<w> <h>"
                then     w*h integers, row-major (y outer 0..h-1, x inner).

   PERFORMANCE NOTE
   ----------------
   The image is handed to the core as a [gimage] record whose [gpix] is an
   O(1) array lookup.  The semantics are identical to the model's
   [gfrom_list] (in-bounds pixel value; 0 out of bounds - [gpix] is only ever
   read in bounds by oob0/wrap), but [gfrom_list] backs [gpix] with a LIST and
   indexes it via [nth], so every pixel read there is O(index) and the whole
   pipeline degrades to O(N^2).  Array backing makes each read O(1).

   Encoding configuration (must mirror the Python side):
     adjacency      = 'all'         -> all_adjacent = true
     threshold      = 0
     bounding_box   = default       -> (x_min,y_min,x_max,y_max) = (1,1,w-2,h-2)
     grid_style     = 'hex'
     packing_density= 0.5           (grid encoder override)
     pixel_area     = PIXEL_AREA below
*)

open Speckle_core

let pixel_area = 20.0
let density = 0.5
let threshold = 0
let all_adjacent = true

(* ---- build a gimage whose pixel access is O(1) (array-backed). --------
   Identical values to Image.gfrom_list: in-bounds -> arr.(y*w+x), else 0. *)
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
  really_input ic b 0 n;
  close_in ic;
  b

(* ---- BMP loader: returns (w, h, arr) with row 0 = top, values 0..255 ---- *)
let read_bmp path =
  let b = read_all path in
  if Bytes.length b < 54 || Bytes.get b 0 <> 'B' || Bytes.get b 1 <> 'M' then
    failwith "not a BMP file";
  let off    = u32 b 10 in            (* bfOffBits: start of pixel array *)
  let w      = i32 b 18 in
  let h_raw  = i32 b 22 in
  let bpp    = u16 b 28 in
  let comp   = u32 b 30 in
  if comp <> 0 then failwith "unsupported BMP compression (need BI_RGB)";
  let top_down = h_raw < 0 in
  let h = abs h_raw in
  let bytes_pp = bpp / 8 in
  if bpp <> 8 && bpp <> 24 && bpp <> 32 then
    failwith (Printf.sprintf "unsupported BMP bit depth: %d" bpp);
  let row_size = ((w * bytes_pp + 3) / 4) * 4 in   (* 4-byte aligned rows *)
  let arr = Array.make (w * h) 0 in
  for y = 0 to h - 1 do
    let src_row = if top_down then y else h - 1 - y in   (* output top-first *)
    let base = off + src_row * row_size in
    for x = 0 to w - 1 do
      let v =
        if bpp = 8 then
          (* 8-bit grayscale: palette index == intensity for a gray ramp,
             matching PIL 'L'/'P' -> np.asarray on the generator's BMPs. *)
          Char.code (Bytes.get b (base + x))
        else begin
          let p = base + x * bytes_pp in
          let bl = Char.code (Bytes.get b p) in       (* BGR(A) order *)
          let gr = Char.code (Bytes.get b (p+1)) in
          let rd = Char.code (Bytes.get b (p+2)) in
          if rd = gr && gr = bl then rd                (* already gray *)
          else (299 * rd + 587 * gr + 114 * bl) / 1000 (* ITU-R 601 luma *)
        end
      in
      arr.(y * w + x) <- v
    done
  done;
  (w, h, arr)

(* ---- original plain-text loader -> (w, h, arr) -------------------------- *)
let read_text path =
  let ic = open_in path in
  let first = input_line ic in
  let w, h = Scanf.sscanf first " %d %d" (fun a b -> (a, b)) in
  let n = w * h in
  let buf = Buffer.create 4096 in
  (try while true do Buffer.add_channel buf ic 4096 done with End_of_file -> ());
  close_in ic;
  let toks = List.filter (fun s -> s <> "")
               (String.split_on_char ' '
                  (String.map (fun c -> if c='\n'||c='\t'||c='\r' then ' ' else c)
                     (Buffer.contents buf))) in
  let arr = Array.make n 0 in
  List.iteri (fun i s -> if i < n then arr.(i) <- int_of_string s) toks;
  let got = List.length toks in
  assert (got = n);
  (w, h, arr)

(* ---- format dispatch: BMP magic / .bmp extension, else text ------------- *)
let read_image path =
  let is_bmp_ext = Filename.check_suffix (String.lowercase_ascii path) ".bmp" in
  let magic_bm =
    try let ic = open_in_bin path in
        let ok = (try input_char ic = 'B' && input_char ic = 'M'
                  with End_of_file -> false) in
        close_in ic; ok
    with _ -> false in
  if is_bmp_ext || magic_bm then read_bmp path else read_text path

let () =
  (* Larger minor heap + higher space_overhead: the solver keeps the
     N-entry memo map and the rebuilt coordinate list live during the
     accounting pass, so the default GC otherwise rescans a big heap
     repeatedly.  This alone roughly halves wall time at 2048x2048. *)
  Gc.set { (Gc.get ()) with
           Gc.minor_heap_size = 64 * 1024 * 1024 / 8;   (* ~64 MB words *)
           Gc.space_overhead  = 400 };
  let in_path = Sys.argv.(1) in
  let out_path = Sys.argv.(2) in
  let (w, h, data) = read_image in_path in
  let img = make_image w h data in
  (* peaks within default bounding box (1,1,w-2,h-2) *)
  let ps = peaks img threshold all_adjacent 1 (w-2) 1 (h-2) in
  (* sort peaks by (x,y) for stable comparison *)
  let ps = List.sort (fun ((x1,y1),_) ((x2,y2),_) ->
             if x1<>x2 then compare x1 x2 else compare y1 y2) ps in
  (* build the peak-weight map image (image_np in the grid encoder) *)
  let pm = Array.make (w*h) 0 in
  List.iter (fun ((x,y),wt) -> if y>=0 && y<h && x>=0 && x<w then pm.(y*w+x) <- wt) ps;
  let peakmap = make_image w h pm in
  (* grid encoding (hex, density 0.5) *)
  let bits = grid_encode GHex peakmap img pixel_area density in
  (* write JSON *)
  let oc = open_out out_path in
  Printf.fprintf oc "{\n";
  Printf.fprintf oc "  \"w\": %d, \"h\": %d,\n" w h;
  Printf.fprintf oc "  \"peaks\": [";
  List.iteri (fun i ((x,y),wt) ->
    if i>0 then Printf.fprintf oc ", ";
    Printf.fprintf oc "[%d, %d, %d]" x y wt) ps;
  Printf.fprintf oc "],\n";
  Printf.fprintf oc "  \"bits\": [";
  List.iteri (fun i b ->
    if i>0 then Printf.fprintf oc ", ";
    Printf.fprintf oc "%d" (if b then 1 else 0)) bits;
  Printf.fprintf oc "]\n}\n";
  close_out oc;
  Printf.printf "%s -> %d peaks, %d bits\n" (Filename.basename in_path)
    (List.length ps) (List.length bits)
