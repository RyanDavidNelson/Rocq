(* ===================================================================== *)
(*  Image.v                                                              *)
(*                                                                       *)
(*  Shared image types and the *exact* coordinate/border semantics used  *)
(*  by the two halves of the original system:                            *)
(*                                                                       *)
(*    - the C extractor (speckle.c) reads neighbours with an explicit    *)
(*      "out-of-bounds => clamp to self, value 0" rule (branchless        *)
(*      `val = in_bounds * intensity`).  Modelled by [oob0].             *)
(*                                                                       *)
(*    - the Python encoders (grid_encoding.py / angle_encoding.py) read   *)
(*      orig_np[y, x] with raw numpy indexing, so NEGATIVE indices wrap   *)
(*      around (numpy semantics) and there is no try/except in the grid   *)
(*      encoder.  Modelled by [wrap].  See the WARNING on [wrap]: this    *)
(*      reproduces numpy's negative-index wraparound but treats indices   *)
(*      with |i| >= dim by further wrapping, whereas numpy would raise    *)
(*      IndexError.  This is a genuine ambiguity / latent-bug surface in  *)
(*      the source and is flagged here for confirmation.                 *)
(*                                                                       *)
(*  Coordinates are [Z] because the encoders form negative indices       *)
(*  (e.g. floor(cy - radius) can be < 0); image dimensions are [nat].    *)
(* ===================================================================== *)

From Coq Require Import ZArith List Lia Bool.
Import ListNotations.
Local Open Scope Z_scope.

(* A grayscale image: width, height, and a pixel function on Z-coords.
   [gpix] is only relied upon within bounds; the access wrappers below
   impose the border semantics. *)
Record gimage := mkGImage {
  gw   : nat;
  gh   : nat;
  gpix : Z -> Z -> nat
}.

Definition zw (img : gimage) : Z := Z.of_nat (gw img).
Definition zh (img : gimage) : Z := Z.of_nat (gh img).

(* In-bounds test. *)
Definition inb (img : gimage) (x y : Z) : bool :=
  (0 <=? x) && (x <? zw img) && (0 <=? y) && (y <? zh img).

(* ---- Extractor border semantics (speckle.c): OOB reads as 0. ---- *)
Definition oob0 (img : gimage) (x y : Z) : nat :=
  if inb img x y then gpix img x y else 0%nat.

(* ---- numpy-encoder border semantics: negative-index wraparound. ----
   Python/numpy a[-1] = a[n-1]; Coq's Z.modulo uses the sign of the
   divisor (floored), so (-1) mod n = n-1 for n>0, matching numpy.
   WARNING: numpy raises IndexError for |i| >= n; here we wrap fully. *)
Definition wrapidx (i : Z) (n : nat) : Z :=
  if Nat.eqb n 0 then 0 else Z.modulo i (Z.of_nat n).

Definition wrap (img : gimage) (x y : Z) : nat :=
  gpix img (wrapidx x (gw img)) (wrapidx y (gh img)).

(* Build a concrete image from row-major data (handy for sanity checks). *)
Definition gfrom_list (w h : nat) (d : list nat) : gimage :=
  mkGImage w h
    (fun x y =>
       if (0 <=? x) && (x <? Z.of_nat w) && (0 <=? y) && (y <? Z.of_nat h)
       then nth (Z.to_nat (y * Z.of_nat w + x)) d 0%nat
       else 0%nat).

(* ===================================================================== *)
(*  Adjacency / offset orderings -- ORDER IS SIGNIFICANT.                *)
(*                                                                       *)
(*  The C extractor's tie-breaking (`explore_path`) depends on the order *)
(*  in which offsets are scanned, so the C orderings must be preserved   *)
(*  verbatim.  The Python `_get_adjacency_offsets` (used only by         *)
(*  `_merge_peaks`, where offsets test set-membership) uses a DIFFERENT  *)
(*  order; for merging the order is immaterial, but we keep it faithful. *)
(*                                                                       *)
(*  All offsets are (x_off, y_off).                                      *)
(* ===================================================================== *)

(* speckle.c:  offset_t cardinal[] = {{0,1},{1,0},{0,-1},{-1,0}}; *)
Definition c_cardinal : list (Z * Z) :=
  [ (0,1); (1,0); (0,-1); (-1,0) ].

(* speckle.c:  offset_t all[] = {{0,1},{1,1},{1,0},{1,-1},{0,-1},{-1,-1},{-1,0},{-1,1}}; *)
Definition c_all : list (Z * Z) :=
  [ (0,1); (1,1); (1,0); (1,-1); (0,-1); (-1,-1); (-1,0); (-1,1) ].

(* peaks_processing.py _get_adjacency_offsets('cardinal') *)
Definition py_cardinal : list (Z * Z) :=
  [ (-1,0); (0,-1); (1,0); (0,1) ].

(* peaks_processing.py _get_adjacency_offsets('all') *)
Definition py_all : list (Z * Z) :=
  [ (-1,0); (-1,-1); (0,-1); (1,-1); (1,0); (1,1); (0,1); (-1,1) ].

(* The C extractor selects between these via the `all_adjacent` flag,
   which `_get_peaks` sets to (adjacency == 'all'). *)
Definition c_offsets (all_adjacent : bool) : list (Z * Z) :=
  if all_adjacent then c_all else c_cardinal.

Definition py_offsets (all_adjacent : bool) : list (Z * Z) :=
  if all_adjacent then py_all else py_cardinal.
