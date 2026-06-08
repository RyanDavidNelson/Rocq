(* ===================================================================== *)
(*  GridEncode.v                                                         *)
(*                                                                       *)
(*  EXACT model of grid_encoding.py:                                     *)
(*    OPUF_Algorithm_Grid_Encoding._get_grid_element_encoding and        *)
(*    ._get_grid_encoding.                                               *)
(*                                                                       *)
(*  The class tiles the image with circular regions (centres from        *)
(*  _get_element_grid, in Peaks.v) and emits one bit per region: 1 iff   *)
(*  some peak-bearing, positive-intensity pixel inside the region's      *)
(*  floor/ceil bounding box lies within `radius` of the centre, AFTER    *)
(*  the sub-pixel refinement.                                            *)
(*                                                                       *)
(*  Faithfulness notes (mirrored verbatim from the photographed source): *)
(*   - The ACTIVE branch is the sub-pixel version; the simpler           *)
(*     "distance only" branch is commented out ('''...''') in the        *)
(*     original, so it is NOT modelled here.                             *)
(*   - image_np = peakmap (peak-weight map), orig_np = grayscale image.  *)
(*   - orig_np[y, x-1] etc. use raw numpy indexing with NO try/except,   *)
(*     so negative indices wrap (numpy) -- modelled by Image.wrap.  The  *)
(*     case |index| >= dim (numpy would IndexError) is the documented    *)
(*     latent-bug surface; see the WARNING on Image.wrap.                *)
(*   - The grid class overrides packing_density to 0.5 (passed as the    *)
(*     `density` argument here); grid_style defaults to 'hex'.           *)
(*   - astype/int() truncation of orig_np is already baked into the      *)
(*     pixel values (nat) produced upstream by Speckle.v.                *)
(* ===================================================================== *)

From Coq Require Import ZArith List Lia Bool Reals.
Import ListNotations.
From SpecklePUF Require Import Image Peaks.

Local Open Scope R_scope.

(* floor / ceil of a real as an integer:  ceil x = - floor (-x). *)
Definition floorZ (x : R) : Z := Int_part x.
Definition ceilZ  (x : R) : Z := (- Int_part (- x))%Z.

(* inclusive integer range [lo .. hi]. *)
Definition zseq_incl (lo hi : Z) : list Z :=
  map (fun i => (lo + Z.of_nat i)%Z) (seq 0 (Z.to_nat (hi - lo + 1))).

(* Sub-pixel offset from a neighbour pair around centre intensity `point`,
   exactly as in the source:
     0                  if a == b
     -(a / (2*point))   if a >  b
      b / (2*point)     otherwise.
   For x: (a,b) = (left, right).   For y: (a,b) = (up, down). *)
Definition subpix_off (a b point : nat) : R :=
  if Nat.eqb a b then 0
  else if Nat.ltb b a               (* a > b *)
       then - (INR a / (2 * INR point))
       else INR b / (2 * INR point).

(* _get_grid_element_encoding(center=(cx,cy), radius, image_np, orig_np). *)
Definition grid_element_encoding (peakmap orig : gimage)
                                 (cx cy radius : R) : bool :=
  let x_min := floorZ (cx - radius) in
  let x_max := ceilZ  (cx + radius) in
  let y_min := floorZ (cy - radius) in
  let y_max := ceilZ  (cy + radius) in
  existsb
    (fun xy =>
       let '(x_tmp, y_tmp) := xy in
       let point := wrap orig x_tmp y_tmp in
       let left  := wrap orig (x_tmp - 1) y_tmp in
       let right := wrap orig (x_tmp + 1) y_tmp in
       let up    := wrap orig x_tmp (y_tmp - 1) in
       let down  := wrap orig x_tmp (y_tmp + 1) in
       if (Nat.ltb 0 (wrap peakmap x_tmp y_tmp)) && (Nat.ltb 0 point)
       then
         let x_off := subpix_off left right point in
         let y_off := subpix_off up down point in
         let dx := IZR x_tmp + x_off - cx in
         let dy := IZR y_tmp + y_off - cy in
         let dist := sqrt (dx * dx + dy * dy) in
         if Rle_dec dist radius then true else false
       else false)
    (* y outer, x inner -- matches the source loop nesting; existsb makes
       the iteration order immaterial to the resulting bit. *)
    (flat_map (fun y => map (fun x => (x, y)) (zseq_incl x_min x_max))
              (zseq_incl y_min y_max)).

(* _get_grid_encoding: radius = sqrt(pixel_area/pi); one bit per element. *)
Definition grid_encode (style : grid_style) (peakmap orig : gimage)
                       (pixel_area density : R) : list bool :=
  let radius := radius_of_area pixel_area in
  map (fun c => let '(cx, cy) := c in
                grid_element_encoding peakmap orig cx cy radius)
      (element_grid style peakmap radius density).

(* Sanity: the bitstring has exactly one bit per grid element. *)
Lemma grid_encode_length :
  forall style peakmap orig pa d,
    length (grid_encode style peakmap orig pa d) =
    length (element_grid style peakmap (radius_of_area pa) d).
Proof. intros. unfold grid_encode. now rewrite map_length. Qed.

Close Scope R_scope.
