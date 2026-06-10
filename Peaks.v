(* ===================================================================== *)
(*  Peaks.v                                                              *)
(*                                                                       *)
(*  EXACT functional model of the speckle extractor's DEFAULT mode       *)
(*  (speckle.c get_speckles, algorithm_variant == GS_DEFAULT, used by     *)
(*  peaks_processing.py _get_peaks).  EXTRACT_REGIONS is built in         *)
(*  unconditionally -- this models the speckle.h build with              *)
(*  `#define EXTRACT_REGIONS 1`, i.e. explore_path + explore_region.      *)
(*                                                                       *)
(*  Only the C `cardinal[]` / `all[]` offset arrays are used (from        *)
(*  Image.v: c_cardinal / c_all, selected by c_offsets all_adjacent).    *)
(*  GS_SIMPLE and the Python _merge_peaks / _get_adjacency_offsets        *)
(*  post-steps are dead code and have been removed.                      *)
(*                                                                       *)
(*  ---- What the C does (DEFAULT + EXTRACT_REGIONS) -------------------  *)
(*  For every pixel the main loop calls explore_path, which "ascends" to  *)
(*  the FIRST strictly-greater neighbour in offset-scan order            *)
(*  (branchless `replace = val > move_intensity`), OOB neighbours read    *)
(*  as 0.  The recursion memoises into solved_map; the value returned     *)
(*  for a pixel is a speckle INDEX (>= BEGIN_SOLVE_REGION = 2) or a       *)
(*  discard marker (UNVISITED 0 / UNUSED_REGION 1).  Per pixel:           *)
(*                                                                       *)
(*   * STRICT local maximum (no neighbour >= it: equal_ctr == 0 and       *)
(*     move_intensity == intensity): solves to itself, index             *)
(*     GET_INDEX(x,y).                                                    *)
(*                                                                       *)
(*   * PLATEAU (>=1 in-bounds neighbour equal, none strictly greater:     *)
(*     equal_ctr > 0 and move_intensity == intensity): explore_region     *)
(*     floods the connected component of EQUAL-intensity in-bounds        *)
(*     pixels (same offsets).  If ANY pixel of that component has an      *)
(*     in-bounds neighbour of STRICTLY GREATER intensity, the whole       *)
(*     region ascends and is discarded (every member -> UNUSED_REGION);   *)
(*     otherwise the region is a flat-topped maximum and every member     *)
(*     solves to ONE index, GET_INDEX(round(mean x), round(mean y)).      *)
(*                                                                       *)
(*   * ASCEND (move_intensity > intensity): solves to whatever the        *)
(*     strictly-greater neighbour (move_x, move_y) solves to.             *)
(*                                                                       *)
(*  A speckle's WEIGHT is the number of grid pixels that solve to its     *)
(*  index (the basin size, counting pixels that ascend into it).  Note    *)
(*  the asymmetry the C exhibits and that this model reproduces: in a     *)
(*  DISCARDED region, members that themselves have a greater neighbour    *)
(*  re-ascend out to a higher peak (and count toward it), while members   *)
(*  with no greater neighbour are dropped.  After the loop, a speckle is  *)
(*  kept iff its index location is in the bounding box                    *)
(*  [x_min,x_max] x [y_min,y_max] AND its weight > threshold.             *)
(*                                                                       *)
(*  ---- Why a pure recursion equals the stateful C ---------------------  *)
(*  explore_path is deterministic and idempotent: solved_map only         *)
(*  memoises the unique result, so the un-memoised recursion below        *)
(*  computes the same value.  Ascent strictly increases intensity, so it  *)
(*  terminates; region exploration is a terminating connected-component   *)
(*  flood.  The region's connected EQUAL-intensity component and its      *)
(*  centroid are independent of which member seeds the exploration, so    *)
(*  every member (and every external pixel ascending in) resolves to the  *)
(*  same index, exactly as the C's one-shot region assignment does.      *)
(* ===================================================================== *)

From Coq Require Import ZArith List Lia Bool Reals.
Import ListNotations.
From SpecklePUF Require Import Image.

Local Open Scope Z_scope.

Definition coord := (Z * Z)%type.

Definition coord_eqb (a b : coord) : bool :=
  (fst a =? fst b) && (snd a =? snd b).
Definition cmem (c : coord) (l : list coord) : bool := existsb (coord_eqb c) l.

Definition zrange (k : nat) : list Z := map Z.of_nat (seq 0 k).

(* Grid coordinates in the C traversal order: x outer (0..w-1), y inner. *)
Definition gcoords (img : gimage) : list coord :=
  flat_map (fun x => map (fun y => (x, y)) (zrange (gh img))) (zrange (gw img)).

Definition inbox (xmin xmax ymin ymax x y : Z) : bool :=
  (xmin <=? x) && (x <=? xmax) && (ymin <=? y) && (y <=? ymax).

(* round(a/b) (C `round`, half away from zero); a,b >= 0 here, so this is
   round-half-up.  Used for the region centroid GET_INDEX coordinate. *)
Definition zround_div (a : Z) (b : nat) : Z :=
  if Nat.eqb b 0 then 0 else (2 * a + Z.of_nat b) / (2 * Z.of_nat b).

(* ===================================================================== *)
(*  explore_path's offset scan                                           *)
(* ===================================================================== *)

(* State = (move_intensity, move_x, move_y, equal_ctr).  `replace` is
   strict (val > move_intensity), so on ties the FIRST occurrence wins;
   equal_ctr counts in-bounds neighbours equal to move_intensity since the
   last replace (`equal_ctr = (!replace)*(equal_ctr + equal)`); OOB
   neighbours contribute value 0 and are never "equal". *)
Definition scan (img : gimage) (offs : list coord) (x y : Z)
  : (nat * Z * Z * nat) :=
  fold_left
    (fun st o =>
       let '(mint, mx, my, ec) := st in
       let xt := x + fst o in
       let yt := y + snd o in
       let ib := inb img xt yt in
       let val := oob0 img xt yt in
       let replace := Nat.ltb mint val in
       let equal := (Nat.eqb val mint) && ib in
       let ec' := if replace then 0%nat else (ec + (if equal then 1 else 0))%nat in
       let mint' := if replace then val else mint in
       let mx' := if replace then xt else mx in
       let my' := if replace then yt else my in
       (mint', mx', my', ec'))
    offs (oob0 img x y, x, y, 0%nat).

(* The three explore_path outcomes (before region handling). *)
Inductive sres := RSolved (p : coord) | RPlateau | RAscend (p : coord).

Definition classify (img : gimage) (offs : list coord) (x y : Z) : sres :=
  let '(mint, mx, my, ec) := scan img offs x y in
  if Nat.eqb mint (oob0 img x y)            (* no strictly-greater neighbour *)
  then (if Nat.eqb ec 0 then RSolved (x, y) (* strict local maximum *)
        else RPlateau)                      (* flat: >=1 equal neighbour *)
  else RAscend (mx, my).                     (* ascend to first greater *)

(* ===================================================================== *)
(*  explore_region : flat connected component, ascend test, centroid     *)
(* ===================================================================== *)

Definition floodfuel (img : gimage) (offs : list coord) : nat :=
  S (gw img * gh img * (S (length offs))).

(* a neighbour belongs to the region iff it is in-bounds and has exactly
   the region intensity ri (matches `equal = (val==intensity) & in_bounds`). *)
Definition same_int (img : gimage) (ri : nat) (q : coord) : bool :=
  inb img (fst q) (snd q) && Nat.eqb (oob0 img (fst q) (snd q)) ri.

(* DFS flood over the equal-intensity adjacency; returns the component. *)
Fixpoint rflood (img : gimage) (offs : list coord) (ri : nat)
                (fuel : nat) (stack visited : list coord) : list coord :=
  match fuel with
  | O => visited
  | S f =>
    match stack with
    | [] => visited
    | p :: rest =>
      if cmem p visited then rflood img offs ri f rest visited
      else
        let nbrs := map (fun o => (fst p + fst o, snd p + snd o)) offs in
        let good := filter (fun q => same_int img ri q && negb (cmem q visited)) nbrs in
        rflood img offs ri f (good ++ rest) (p :: visited)
    end
  end.

(* The connected EQUAL-intensity region containing seed s (s in-bounds). *)
Definition region (img : gimage) (offs : list coord) (s : coord) : list coord :=
  rflood img offs (oob0 img (fst s) (snd s)) (floodfuel img offs) [s] [].

(* does pixel p have an in-bounds neighbour strictly greater than ri?
   (`ascend = val > max_intensity`, max starting at ri; OOB val is 0). *)
Definition pixel_ascends (img : gimage) (offs : list coord) (ri : nat)
                         (p : coord) : bool :=
  existsb (fun o =>
             let qx := fst p + fst o in
             let qy := snd p + snd o in
             inb img qx qy && Nat.ltb ri (oob0 img qx qy))
          offs.

(* the region ascends (is discarded) iff ANY member has a greater neighbour. *)
Definition region_ascends (img : gimage) (offs : list coord) (ri : nat)
                          (R : list coord) : bool :=
  existsb (pixel_ascends img offs ri) R.

(* GET_INDEX(round(mean x), round(mean y)) location = rounded centroid. *)
Definition region_centroid (R : list coord) : coord :=
  let cnt := length R in
  let sx := fold_right (fun q a => fst q + a) 0 R in
  let sy := fold_right (fun q a => snd q + a) 0 R in
  (zround_div sx cnt, zround_div sy cnt).

(* ===================================================================== *)
(*  solve : the index (as a coordinate) a pixel resolves to, or None     *)
(*          for a discard (UNVISITED / UNUSED_REGION).                    *)
(* ===================================================================== *)

Fixpoint solve (img : gimage) (offs : list coord) (fuel : nat) (p : coord)
  : option coord :=
  match classify img offs (fst p) (snd p) with
  | RSolved q => Some q
  | RPlateau =>
      let ri := oob0 img (fst p) (snd p) in
      let R := region img offs p in
      if region_ascends img offs ri R then None
      else Some (region_centroid R)
  | RAscend q => match fuel with
                 | O => None
                 | S f => solve img offs f q
                 end
  end.

(* Ascent strictly increases intensity, so a chain visits each pixel at
   most once; gw*gh+1 is a safe fuel bound. *)
Definition fuel0 (img : gimage) : nat := S (gw img * gh img).
Definition solveP (img : gimage) (offs : list coord) (p : coord) : option coord :=
  solve img offs (fuel0 img) p.

(* ===================================================================== *)
(*  Speckle accounting : basin weights + final threshold/box filter      *)
(* ===================================================================== *)

(* Basin size of a candidate index c: how many grid pixels solve to c. *)
Definition weight (img : gimage) (offs : list coord) (c : coord) : nat :=
  length (filter (fun p => match solveP img offs p with
                           | Some q => coord_eqb q c
                           | None => false
                           end)
                 (gcoords img)).

(* Distinct speckle indices = distinct solveP results over the grid, in
   first-seen (C traversal) order. *)
Definition candidates (img : gimage) (offs : list coord) : list coord :=
  fold_left
    (fun acc p => match solveP img offs p with
                  | Some q => if cmem q acc then acc else acc ++ [q]
                  | None => acc
                  end)
    (gcoords img) [].

(* GS_DEFAULT (EXTRACT_REGIONS) speckle list: index in the bounding box
   AND basin weight strictly greater than the threshold. *)
Definition peaks_default (img : gimage) (t : nat) (offs : list coord)
                         (xmin xmax ymin ymax : Z) : list (Z * Z * nat) :=
  fold_right
    (fun c acc =>
       let '(cx, cy) := c in
       if inbox xmin xmax ymin ymax cx cy && Nat.ltb t (weight img offs c)
       then (cx, cy, weight img offs c) :: acc
       else acc)
    [] (candidates img offs).

(* ---- Public entry points, matching the Python _get_peaks call. -------
   `all_adjacent` selects the C offset array (c_offsets), exactly as
   peaks_processing.py passes (adjacency == 'all'). *)
Definition peaks (img : gimage) (t : nat) (all_adjacent : bool)
                 (xmin xmax ymin ymax : Z) : list (Z * Z * nat) :=
  peaks_default img t (c_offsets all_adjacent) xmin xmax ymin ymax.

(* Whole-image bounding box (every in-bounds index admissible). *)
Definition peaks_full (img : gimage) (t : nat) (all_adjacent : bool)
  : list (Z * Z * nat) :=
  peaks img t all_adjacent 0 (zw img - 1) 0 (zh img - 1).

(* ===================================================================== *)
(*  Shared element-grid geometry  (peaks_processing.py)                  *)
(*                                                                       *)
(*  _get_x_y_bounds (default bounding box), np.arange over R, the        *)
(*  square/hex circle-packing of _get_element_grid, and the             *)
(*  radius = sqrt(pixel_area / pi) helper.  These are used by BOTH       *)
(*  encoders (grid and angle), exactly as in the Python where they are   *)
(*  inherited from OPUF_Algorithm_Peaks_Processing.                      *)
(*                                                                       *)
(*  All grid arithmetic is REAL-valued, matching numpy float math.       *)
(* ===================================================================== *)

Local Open Scope R_scope.

(* _get_x_y_bounds with the default bounding_box = (w-2, h-2):
     min_x = int((w-(w-2))/2) = 1,   min_y = 1,
     max_x = w - min_x - 1 = w-2,    max_y = h-2.
   Returned as reals for the float grid math below. *)
Definition gxmin (img : gimage) : R := 1.
Definition gymin (img : gimage) : R := 1.
Definition gxmax (img : gimage) : R := IZR ((zw img) - 2)%Z.
Definition gymax (img : gimage) : R := IZR ((zh img) - 2)%Z.

(* np.arange(start, stop, step): start, start+step, ... while strictly < stop.
   Fuel is generous; the (cur < stop) guard trims any overshoot, so the
   half-open interval (and exact-integer ratios) match numpy. *)
Fixpoint arange_aux (fuel : nat) (cur stop step : R) : list R :=
  match fuel with
  | O => []
  | S f => if Rlt_dec cur stop
           then cur :: arange_aux f (cur + step) stop step
           else []
  end.

Definition arange_count (start stop step : R) : nat :=
  if Rle_dec step 0 then 0%nat
  else (Z.to_nat (up ((stop - start) / step)) + 2)%nat.

Definition arange (start stop step : R) : list R :=
  arange_aux (arange_count start stop step) start stop step.

(* radius from a circular pixel_area:  (pixel_area / pi) ** .5 *)
Definition radius_of_area (pixel_area : R) : R := sqrt (pixel_area / PI).

(* ---- 'square' packing ----
   spacing = .5*sqrt(9*pi*r^2 / density) - 3r
   x_offsets = arange(spacing+r+x_min, x_max-r-spacing, 2*(spacing+r))
   y_offsets likewise
   return [(x,y) for (y,x) in product(y_offsets, x_offsets)]
     => y outer, x inner, emitting (x,y). *)
Definition square_spacing (radius density : R) : R :=
  0.5 * sqrt ((9 * PI * (radius * radius)) / density) - 3 * radius.

Definition square_grid (img : gimage) (radius density : R) : list (R * R) :=
  let sp := square_spacing radius density in
  let xs := arange (sp + radius + gxmin img) (gxmax img - radius - sp)
                   (2 * (sp + radius)) in
  let ys := arange (sp + radius + gymin img) (gymax img - radius - sp)
                   (2 * (sp + radius)) in
  flat_map (fun y => map (fun x => (x, y)) xs) ys.

(* ---- 'hex' packing ----
   h_spacing = (2/9)*((3**.25 * sqrt(14*pi))/sqrt(density) - 9)*r
   v_spacing = sqrt(3)*(r + h_spacing/2)
   x_offsets = arange(h_spacing+2r+x_min, x_max-2*(2r+h_spacing), 2*(h_spacing+r))
   y_offsets = arange(r+y_min+v_spacing/2, y_max-r-v_spacing/2, v_spacing)
   even rows: (x,y); odd rows staggered: (x+r+h_spacing, y). *)
Definition hex_hspacing (radius density : R) : R :=
  (2 / 9) * ((Rpower 3 (1/4) * sqrt (14 * PI)) / sqrt density - 9) * radius.

Definition hex_vspacing (radius hspacing : R) : R :=
  sqrt 3 * (radius + hspacing / 2).

Fixpoint hex_rows (idx : nat) (ys xs : list R) (r hs : R) : list (R * R) :=
  match ys with
  | [] => []
  | y :: ys' =>
      let row := map (fun x => if Nat.even idx
                               then (x, y)
                               else (x + r + hs, y)) xs in
      row ++ hex_rows (S idx) ys' xs r hs
  end.

Definition hex_grid (img : gimage) (radius density : R) : list (R * R) :=
  let hs := hex_hspacing radius density in
  let vs := hex_vspacing radius hs in
  let xs := arange (hs + 2 * radius + gxmin img)
                   (gxmax img - 2 * (2 * radius + hs)) (2 * (hs + radius)) in
  let ys := arange (radius + gymin img + vs / 2)
                   (gymax img - radius - vs / 2) vs in
  hex_rows 0 ys xs radius hs.

Inductive grid_style := GSquare | GHex.

Definition element_grid (style : grid_style) (img : gimage)
                        (radius density : R) : list (R * R) :=
  match style with
  | GSquare => square_grid img radius density
  | GHex    => hex_grid img radius density
  end.

Close Scope R_scope.
