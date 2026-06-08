(* ===================================================================== *)
(*  AngleEncode.v                                                        *)
(*                                                                       *)
(*  EXACT model of angle_encoding.py:                                    *)
(*    OPUF_Algorithm_Angle_Encoding._get_angle, ._get_point_pair,        *)
(*    ._get_angle_element_encoding, and ._angle_encoding.                *)
(*                                                                       *)
(*  Around each grid centre, the expanding-ring search finds the nearest *)
(*  two peaks; the angle between them (atan2) is quantised into          *)
(*  2^num_bits equal slices of [-pi, pi); the slice index is emitted     *)
(*  LSB-first as num_bits bits.                                          *)
(*                                                                       *)
(*  Faithfulness notes (mirrored verbatim from the photographed source): *)
(*   - The ACTIVE _get_point_pair is the last of three variants; the     *)
(*     earlier two ('''...''') are commented out and NOT modelled.       *)
(*   - The ACTIVE search draws `order = list(range(4)); random.shuffle`  *)
(*     once per ring.  random.shuffle is NONDETERMINISTIC, so the result *)
(*     is NOT a pure function of the image.  We make the randomness an   *)
(*     EXPLICIT INPUT: [order : nat -> list nat] supplies the 4-element  *)
(*     permutation used at each ring `dist`.  Pick the identity stream   *)
(*     (fun _ => [0;1;2;3]) to model one particular shuffle outcome.     *)
(*   - np_map[r, c] uses raw numpy indexing inside a try/except that     *)
(*     swallows IndexError: negative indices WRAP (numpy), indices with  *)
(*     |i| >= dim raise IndexError and are SKIPPED.  Modelled by         *)
(*     [np_get] (Some wrapped-value in numpy's valid range [-dim,dim-1], *)
(*     None outside).  The stored coordinate is the RAW (possibly        *)
(*     negative) index, exactly as the source appends it.               *)
(*   - center is rounded with Python 3 round() = round-half-to-EVEN      *)
(*     (banker's rounding); modelled by [pyround].                       *)
(*   - The sub-pixel offset block in _get_angle_element_encoding is      *)
(*     commented out, so orig_np is unused by the active code and is     *)
(*     omitted here.                                                     *)
(*   - `while True` is bounded by an explicit ring-count [fuel]; Python  *)
(*     relies on >= 2 peaks existing.  With enough fuel and >= 2 peaks   *)
(*     the model matches; otherwise it returns the all-false default.    *)
(*   - atan2 is built from stdlib [atan] (no atan2 in Coq.Reals); the    *)
(*     branch structure matches the C/Python atan2 convention, range     *)
(*     (-pi, pi], with atan2(0,0) = 0 as in math.atan2.                  *)
(* ===================================================================== *)

From Coq Require Import ZArith List Lia Bool Reals.
Import ListNotations.
From SpecklePUF Require Import Image Peaks.

Local Open Scope Z_scope.

(* ---------- real-valued helpers (atan2 and angle binning) ---------- *)
Section RealHelpers.
Local Open Scope R_scope.

(* atan2(y, x) from stdlib atan, matching math.atan2 quadrants;
   range (-pi, pi], atan2(0,0) = 0. *)
Definition atan2 (y x : R) : R :=
  if Rlt_dec 0 x then atan (y / x)
  else if Rlt_dec x 0 then
         (if Rle_dec 0 y then atan (y / x) + PI else atan (y / x) - PI)
  else (* x = 0 *)
         (if Rlt_dec 0 y then PI / 2
          else if Rlt_dec y 0 then - (PI / 2)
          else 0).

(* _get_angle(start=(x0,y0), point=(x1,y1)) = atan2(y1-y0, x1-x0). *)
Definition get_angle (x0 y0 x1 y1 : Z) : R :=
  atan2 (IZR (y1 - y0)) (IZR (x1 - x0)).

(* find the half-open slice [lo_i, hi_i) containing `a`, scanning i upward
   exactly as the source loop (which breaks on the first match). *)
Fixpoint find_bin (k i : nat) (a bw : R) : option nat :=
  match k with
  | O => None
  | S k' =>
      let lo := - PI + INR i * bw in
      let hi := - PI + INR (S i) * bw in
      if (if Rle_dec lo a then true else false)
           && (if Rlt_dec a hi then true else false)
      then Some i
      else find_bin k' (S i) a bw
  end.

(* the angle, after the `if angle == pi: angle = -pi` remap. *)
Definition remap_pi (a : R) : R :=
  if Rle_dec PI a then (if Rle_dec a PI then - PI else a) else a.

Definition angle_bin (num_bits : nat) (angle : R) : option nat :=
  let n := Nat.pow 2 num_bits in
  let bw := (2 * PI) / INR n in
  find_bin n 0 (remap_pi angle) bw.

End RealHelpers.

(* bits of slice index i, LSB-first:  (i & 2^place) != 0  for place<num_bits. *)
Definition bits_of_bin (num_bits i : nat) : list bool :=
  map (fun place => Nat.testbit i place) (seq 0 num_bits).

Definition angle_element_bits (num_bits : nat) (angle : R) : list bool :=
  match angle_bin num_bits angle with
  | Some i => bits_of_bin num_bits i
  | None   => repeat false num_bits   (* unreachable for atan2 output *)
  end.

(* ---------- Python 3 round(): round half to even ---------- *)
Definition pyround (x : R) : Z :=
  let f := Int_part x in                 (* floor x *)
  let r := (x - IZR f)%R in              (* fractional part in [0,1) *)
  if Rlt_dec r (1/2)%R then f
  else if Rlt_dec (1/2)%R r then (f + 1)%Z
  else (* r = 1/2 *) if Z.even f then f else (f + 1)%Z.

(* ---------- numpy access with IndexError vs negative-wrap ---------- *)
(* numpy a[i] is valid for i in [-dim, dim-1]: negative wraps, otherwise
   IndexError.  Returns None where numpy would raise (and the source's
   try/except would skip the candidate). *)
Definition np_get (img : gimage) (col row : Z) : option nat :=
  let w := zw img in
  let h := zh img in
  if (- w <=? col) && (col <? w) && (- h <=? row) && (row <? h)
  then Some (wrap img col row)
  else None.

(* ---------- expanding-ring search (_get_point_pair, active variant) ---------- *)

(* candidate coordinate for ring `d`, step `i`, direction `o` (0=N,1=S,2=E,3=W),
   exactly as the appended (x, y) in the source. *)
Definition dir_coord (cx cy d : Z) (i : nat) (o : nat) : (Z * Z) :=
  let zi := Z.of_nat i in
  match o with
  | 0%nat => (cx - d + zi + 1, cy - d)        (* North *)
  | 1%nat => (cx + d - zi - 1, cy + d)        (* South *)
  | 2%nat => (cx + d, cy - d + zi + 1)        (* East  *)
  | _     => (cx - d, cy + d - zi - 1)        (* West  *)
  end.

(* all candidates appended on ring `d`, in source order: i outer, o (the
   shuffled order) inner; only positions with np_get = Some v, 0 < v. *)
Definition ring_candidates (np_map : gimage) (cx cy d : Z) (ord : list nat)
  : list (Z * Z) :=
  flat_map
    (fun i =>
       flat_map
         (fun o =>
            let '(col, row) := dir_coord cx cy d i o in
            match np_get np_map col row with
            | Some v => if Nat.ltb 0 v then [(col, row)] else []
            | None => []
            end)
         ord)
    (seq 0%nat (Z.to_nat (2 * d))).

(* squared distance from the (rounded, integer) centre, then sqrt. *)
Definition cdist (cx cy : Z) (cr : Z * Z) : R :=
  let '(col, row) := cr in
  sqrt (IZR ((col - cx) * (col - cx) + (row - cy) * (row - cy))).

(* stable insertion sort by the real distance key (first tuple component). *)
Fixpoint sins (x : R * Z * Z) (l : list (R * Z * Z)) : list (R * Z * Z) :=
  match l with
  | [] => [x]
  | y :: ys =>
      let '(ex, _, _) := x in
      let '(ey, _, _) := y in
      if Rle_dec ex ey then x :: y :: ys else y :: sins x ys
  end.
Fixpoint ssort (l : list (R * Z * Z)) : list (R * Z * Z) :=
  match l with [] => [] | x :: xs => sins x (ssort xs) end.

(* the while-loop, bounded by `fuel` rings.  Threads `potential` (carried
   candidates whose Euclid distance still exceeds the current ring radius)
   and `found`, exactly as the source. *)
Fixpoint pair_search (fuel : nat) (np_map : gimage) (cx cy : Z)
                     (order : nat -> list nat) (d : Z)
                     (potential : list (Z * Z)) (found : list (R * Z * Z))
  : list (R * Z * Z) :=
  match fuel with
  | O => firstn 2 (ssort found)
  | S f =>
      let pot := potential ++ ring_candidates np_map cx cy d (order (Z.to_nat d)) in
      let withinb := fun cr => if Rle_dec (cdist cx cy cr) (IZR d) then true else false in
      let to_add := filter withinb pot in
      let pot'   := filter (fun cr => negb (withinb cr)) pot in
      let found' := found ++ map (fun cr => let '(col, row) := cr in
                                             (cdist cx cy cr, col, row)) to_add in
      if Nat.ltb 1 (length found')
      then firstn 2 (ssort found')
      else pair_search f np_map cx cy order (d + 1) pot' found'
  end.

(* returns the two nearest peak coordinates, if found. *)
Definition point_pair (fuel : nat) (np_map : gimage) (order : nat -> list nat)
                      (cx_r cy_r : R) : option ((Z * Z) * (Z * Z)) :=
  let cx := pyround cx_r in
  let cy := pyround cy_r in
  match pair_search fuel np_map cx cy order 1 [] [] with
  | (_, x0, y0) :: (_, x1, y1) :: _ => Some ((x0, y0), (x1, y1))
  | _ => None
  end.

(* _get_angle_element_encoding: nearest-pair angle -> num_bits bits. *)
Definition angle_element_encoding (fuel num_bits : nat) (np_map : gimage)
                                  (order : nat -> list nat) (cx cy : R)
  : list bool :=
  match point_pair fuel np_map order cx cy with
  | Some ((x0, y0), (x1, y1)) => angle_element_bits num_bits (get_angle x0 y0 x1 y1)
  | None => repeat false num_bits
  end.

(* _angle_encoding: concatenate num_bits per grid element. *)
Definition angle_encode (style : grid_style) (fuel num_bits : nat)
                        (peakmap : gimage) (order : nat -> list nat)
                        (pixel_area density : R) : list bool :=
  let radius := radius_of_area pixel_area in
  flat_map (fun c => let '(cx, cy) := c in
                     angle_element_encoding fuel num_bits peakmap order cx cy)
           (element_grid style peakmap radius density).

(* Sanity: every grid element contributes exactly num_bits bits, so the
   total length is num_bits * (number of elements). *)
Lemma angle_element_length :
  forall fuel num_bits np_map order cx cy,
    length (angle_element_encoding fuel num_bits np_map order cx cy) = num_bits.
Proof.
  intros. unfold angle_element_encoding.
  destruct (point_pair fuel np_map order cx cy) as [[[x0 y0] [x1 y1]]|].
  - unfold angle_element_bits.
    destruct (angle_bin num_bits (get_angle x0 y0 x1 y1)).
    + unfold bits_of_bin. rewrite map_length, seq_length. reflexivity.
    + apply repeat_length.
  - apply repeat_length.
Qed.

Close Scope Z_scope.
