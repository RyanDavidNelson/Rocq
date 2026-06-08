(* ===================================================================== *)
(*  Peaks.v                                                              *)
(*                                                                       *)
(*  EXACT model of the extractor (speckle.c get_speckles + the Python    *)
(*  _merge_peaks post-step).  Two C variants:                            *)
(*                                                                       *)
(*   GS_DEFAULT (variant 0, used by _get_peaks):                         *)
(*     explore_path makes every pixel ascend, via the offset scan, to    *)
(*     the FIRST strictly-greater neighbour (branchless `replace =       *)
(*     val > move_intensity`); out-of-bounds neighbours read as 0.  A    *)
(*     pixel that is a STRICT local maximum solves to itself.  A pixel    *)
(*     whose maximum is tied with >=1 in-bounds neighbour (a plateau)     *)
(*     is, in the DEFAULT build (EXTRACT_REGIONS is commented out in      *)
(*     speckle.h), marked UNUSED and discarded -- so are the pixels that  *)
(*     ascend into it.  A speckle's WEIGHT is its basin size (number of   *)
(*     pixels solving to it).  Post-loop, only speckles with             *)
(*     weight > threshold and whose location is in-bounds are kept.       *)
(*       [The EXTRACT_REGIONS variant -- plateau -> region midpoint --   *)
(*        is NOT the default build; modelled as a TODO note, not here.]  *)
(*                                                                       *)
(*   GS_SIMPLE (variant 1, used by _get_peaks_simple):                   *)
(*     connected-component flood fill over pixels with intensity >        *)
(*     threshold (offset adjacency, OOB->0 so excluded); one speckle per  *)
(*     component at its ROUNDED centroid, weight = component size; kept   *)
(*     if the centroid is in-bounds.                                     *)
(*                                                                       *)
(*   _merge_peaks (peaks_processing.py): flood-fill connected speckles    *)
(*     (adjacency on the peak coordinates, Python offset order), merge a  *)
(*     component to (mean x, mean y [REAL-valued, per Python `/`],        *)
(*     sum of weights); sort by weight descending.                       *)
(*                                                                       *)
(*  Offsets are passed in explicitly so the caller chooses cardinal/all   *)
(*  with the correct (C vs Python) ordering from Image.v.                *)
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

(* ===================================================================== *)
(*  GS_DEFAULT : ascent / strict local maxima / basin weights            *)
(* ===================================================================== *)

(* The offset scan from explore_path.  State = (move_intensity, move_x,
   move_y, equal_ctr).  `replace` is strict (val > move_intensity), so on
   ties the FIRST occurrence is kept; equal_ctr counts in-bounds equals
   since the last replace; OOB neighbours contribute value 0. *)
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

(* (x,y) is a STRICT local maximum: no in-bounds neighbour >= it. *)
Definition is_smax (img : gimage) (offs : list coord) (x y : Z) : bool :=
  let '(mint, _, _, ec) := scan img offs x y in
  (Nat.eqb mint (oob0 img x y)) && (Nat.eqb ec 0).

Inductive sres := RSolved (p : coord) | RPlateau | RAscend (p : coord).

Definition classify (img : gimage) (offs : list coord) (x y : Z) : sres :=
  let '(mint, mx, my, ec) := scan img offs x y in
  if Nat.eqb mint (oob0 img x y)
  then (if Nat.eqb ec 0 then RSolved (x, y) else RPlateau)
  else RAscend (mx, my).

(* Where does a pixel's ascent terminate?  Some max | None (plateau/discard). *)
Fixpoint solve (img : gimage) (offs : list coord) (fuel : nat) (p : coord)
  : option coord :=
  match classify img offs (fst p) (snd p) with
  | RSolved q => Some q
  | RPlateau => None
  | RAscend q => match fuel with
                 | O => None
                 | S f => solve img offs f q
                 end
  end.

Definition fuel0 (img : gimage) : nat := S (gw img * gh img).
Definition solveP (img : gimage) (offs : list coord) (p : coord) : option coord :=
  solve img offs (fuel0 img) p.

(* Basin size of a candidate maximum c. *)
Definition weight (img : gimage) (offs : list coord) (c : coord) : nat :=
  length (filter (fun p => match solveP img offs p with
                           | Some q => coord_eqb q c
                           | None => false
                           end)
                 (gcoords img)).

(* The GS_DEFAULT speckle list: strict maxima, in-bounds, basin > threshold. *)
Definition peaks_default (img : gimage) (t : nat) (offs : list coord)
                         (xmin xmax ymin ymax : Z) : list (Z * Z * nat) :=
  fold_right
    (fun c acc =>
       let '(cx, cy) := c in
       if (is_smax img offs cx cy)
            && (inbox xmin xmax ymin ymax cx cy)
            && (Nat.ltb t (weight img offs c))
       then (cx, cy, weight img offs c) :: acc
       else acc)
    [] (gcoords img).

Definition peaks_default_full (img : gimage) (t : nat) (offs : list coord)
  : list (Z * Z * nat) :=
  peaks_default img t offs 0 (zw img - 1) 0 (zh img - 1).

(* ===================================================================== *)
(*  GS_SIMPLE : connected-component flood fill                            *)
(* ===================================================================== *)

(* round(a/b), half away from zero; here a,b >= 0 so it's round-half-up. *)
Definition zround_div (a : Z) (b : nat) : Z :=
  if Nat.eqb b 0 then 0 else (2 * a + Z.of_nat b) / (2 * Z.of_nat b).

Definition floodfuel (img : gimage) (offs : list coord) : nat :=
  S (gw img * gh img * (S (length offs))).

(* DFS flood fill: returns visited extended with the component of [stack]. *)
Fixpoint flood (img : gimage) (t : nat) (offs : list coord)
               (fuel : nat) (stack visited : list coord) : list coord :=
  match fuel with
  | O => visited
  | S f =>
    match stack with
    | [] => visited
    | p :: rest =>
      if cmem p visited then flood img t offs f rest visited
      else
        let nbrs := map (fun o => (fst p + fst o, snd p + snd o)) offs in
        let good := filter (fun q => (Nat.ltb t (oob0 img (fst q) (snd q)))
                                       && negb (cmem q visited)) nbrs in
        flood img t offs f (good ++ rest) (p :: visited)
    end
  end.

Definition component (img : gimage) (t : nat) (offs : list coord)
                     (visited : list coord) (seed : coord) : list coord :=
  filter (fun q => negb (cmem q visited))
         (flood img t offs (floodfuel img offs) [seed] visited).

Definition simple_speckles (img : gimage) (t : nat) (offs : list coord)
                           (xmin xmax ymin ymax : Z) : list (Z * Z * nat) :=
  snd (fold_left
         (fun st c =>
            let '(visited, out) := st in
            let '(cx, cy) := c in
            if (Nat.ltb t (oob0 img cx cy)) && negb (cmem c visited)
            then
              let comp := component img t offs visited c in
              let cnt := length comp in
              let sx := fold_right (fun q a => fst q + a) 0 comp in
              let sy := fold_right (fun q a => snd q + a) 0 comp in
              let rx := zround_div sx cnt in
              let ry := zround_div sy cnt in
              if inbox xmin xmax ymin ymax rx ry
              then (comp ++ visited, out ++ [(rx, ry, cnt)])
              else (comp ++ visited, out)
            else st)
         (gcoords img) ([], [])).

Definition simple_speckles_full (img : gimage) (t : nat) (offs : list coord)
  : list (Z * Z * nat) :=
  simple_speckles img t offs 0 (zw img - 1) 0 (zh img - 1).

(* ===================================================================== *)
(*  _merge_peaks  (real-valued merged centroids, sorted by weight desc.)  *)
(* ===================================================================== *)

Definition pk_coord (p : Z * Z * nat) : coord := let '(x, y, _) := p in (x, y).
Definition pk_w (p : Z * Z * nat) : nat := let '(_, _, w) := p in w.
Definition pk_mem (c : coord) (l : list (Z * Z * nat)) : bool :=
  existsb (fun p => coord_eqb (pk_coord p) c) l.

(* flood over the peak-coordinate adjacency graph *)
Fixpoint pflood (peaks : list (Z * Z * nat)) (offs : list coord)
                (fuel : nat) (stack visited : list coord) : list coord :=
  match fuel with
  | O => visited
  | S f =>
    match stack with
    | [] => visited
    | p :: rest =>
      if cmem p visited then pflood peaks offs f rest visited
      else
        let nbrs := map (fun o => (fst p + fst o, snd p + snd o)) offs in
        let good := filter (fun q => (pk_mem q peaks) && negb (cmem q visited)) nbrs in
        pflood peaks offs f (good ++ rest) (p :: visited)
    end
  end.

Definition pcomponent (peaks : list (Z * Z * nat)) (offs : list coord)
                      (visited : list coord) (seed : coord) : list coord :=
  filter (fun q => negb (cmem q visited))
         (pflood peaks offs (S (length peaks * S (length offs))) [seed] visited).

(* weight of a coord within the peak list (0 if absent) *)
Definition wat (peaks : list (Z * Z * nat)) (c : coord) : nat :=
  fold_right (fun p acc => if coord_eqb (pk_coord p) c then (acc + pk_w p)%nat else acc)
             0%nat peaks.

(* weight projection for merged real-valued peaks *)
Definition pk_w_r (p : R * R * nat) : nat := let '(_, _, w) := p in w.

(* insertion sort by weight, descending *)
Fixpoint insert_desc (x : R * R * nat) (l : list (R * R * nat)) : list (R * R * nat) :=
  match l with
  | [] => [x]
  | y :: ys => if Nat.leb (pk_w_r y) (pk_w_r x)
               then x :: y :: ys
               else y :: insert_desc x ys
  end.

Fixpoint sort_desc (l : list (R * R * nat)) : list (R * R * nat) :=
  match l with
  | [] => []
  | x :: xs => insert_desc x (sort_desc xs)
  end.

Definition merge_peaks (peaks : list (Z * Z * nat)) (offs : list coord)
  : list (R * R * nat) :=
  let merged :=
    snd (fold_left
           (fun st p =>
              let '(visited, out) := st in
              let c := pk_coord p in
              if pk_mem c peaks && negb (cmem c visited)
              then
                let comp := pcomponent peaks offs visited c in
                let cnt := length comp in
                let sx := fold_right (fun q a => fst q + a) 0 comp in
                let sy := fold_right (fun q a => snd q + a) 0 comp in
                let wsum := fold_right (fun q a => a + wat peaks q)%nat 0%nat comp in
                let rx := (IZR sx / INR cnt)%R in
                let ry := (IZR sy / INR cnt)%R in
                (comp ++ visited, out ++ [(rx, ry, wsum)])
              else st)
           peaks ([], [])) in
  sort_desc merged.

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
