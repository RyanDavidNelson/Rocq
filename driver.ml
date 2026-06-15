(* driver.ml
   Runs the EXTRACTED Coq core (Peaks.peaks + GridEncode.grid_encode) on a
   speckle image and writes the peaks list and grid encoding to JSON.

   Image file format (plain text):
     line 1:  "<w> <h>"
     then     w*h integers, row-major (y outer 0..h-1, x inner 0..w-1)

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

let read_image path =
  let ic = open_in path in
  let first = input_line ic in
  let w, h = Scanf.sscanf first " %d %d" (fun a b -> (a, b)) in
  let n = w * h in
  let buf = Buffer.create 1024 in
  (try while true do Buffer.add_channel buf ic 4096 done with End_of_file -> ());
  close_in ic;
  let toks = List.filter (fun s -> s <> "")
               (String.split_on_char ' '
                  (String.map (fun c -> if c='\n'||c='\t'||c='\r' then ' ' else c)
                     (Buffer.contents buf))) in
  let data = List.map int_of_string toks in
  assert (List.length data = n);
  (w, h, data)

let () =
  let in_path = Sys.argv.(1) in
  let out_path = Sys.argv.(2) in
  let (w, h, data) = read_image in_path in
  let img = gfrom_list w h data in
  (* peaks within default bounding box (1,1,w-2,h-2) *)
  let ps = peaks img threshold all_adjacent 1 (w-2) 1 (h-2) in
  (* sort peaks by (x,y) for stable comparison *)
  let ps = List.sort (fun ((x1,y1),_) ((x2,y2),_) ->
             if x1<>x2 then compare x1 x2 else compare y1 y2) ps in
  (* build the peak-weight map image (image_np in the grid encoder) *)
  let pm = Array.make (w*h) 0 in
  List.iter (fun ((x,y),wt) -> if y>=0 && y<h && x>=0 && x<w then pm.(y*w+x) <- wt) ps;
  let peakmap = gfrom_list w h (Array.to_list pm) in
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
