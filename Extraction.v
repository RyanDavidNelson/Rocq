(* ===================================================================== *)
(*  Extraction.v                                                         *)
(*  Extract the COMPUTATIONAL core of Peaks.v + GridEncode.v to OCaml.    *)
(*  Coq reals are mapped to OCaml [float]; nat and Z to native [int].     *)
(*  The only non-trivial mappings are floored Z.div / Z.modulo (Coq's    *)
(*  reals/integers are floored; OCaml's are truncated) which matters for  *)
(*  Image.wrap's numpy negative-index semantics.                         *)
(* ===================================================================== *)

From Coq Require Import ZArith List Reals QArith.
From Coq Require Import ClassicalDedekindReals.
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlNatInt.
From Coq Require Import ExtrOcamlZInt.
From SpecklePUF Require Import Image Peaks GridEncode.

(* ---- nat comparisons as O(1) int ops (override any recursive defs) --- *)
Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.even => "(fun n -> n mod 2 = 0)".
Extract Inlined Constant Nat.odd  => "(fun n -> n mod 2 <> 0)".

(* ---- floored Z.div / Z.modulo to match Coq (OCaml's are truncated) --- *)
Extract Constant Z.div =>
  "(fun a b -> if b = 0 then 0 else
     let q = a / b and r = a mod b in
     if r <> 0 && (r < 0) <> (b < 0) then q - 1 else q)".
Extract Constant Z.modulo =>
  "(fun a b -> if b = 0 then a else
     let r = a mod b in
     if r <> 0 && (r < 0) <> (b < 0) then r + b else r)".

(* ---- The real-number layer mapped onto OCaml float -------------------- *)
Extract Inlined Constant R   => "float".
Extract Inlined Constant R0  => "0.0".
Extract Inlined Constant R1  => "1.0".
Extract Inlined Constant Rplus  => "(+.)".
Extract Inlined Constant Rmult  => "( *. )".
Extract Inlined Constant Rminus => "(-.)".
Extract Inlined Constant Ropp   => "(~-.)".
Extract Inlined Constant Rdiv   => "(/.)".
Extract Inlined Constant Rinv   => "(fun x -> 1.0 /. x)".
Extract Inlined Constant IZR    => "float_of_int".
Extract Inlined Constant INR    => "float_of_int".
Extract Inlined Constant sqrt   => "Stdlib.sqrt".
Extract Inlined Constant PI     => "(4.0 *. atan 1.0)".
Extract Inlined Constant Rpower => "(fun x y -> exp (y *. log x))".

(* floor / ceil helpers (Coq Int_part = floor, up = floor + 1) *)
Extract Inlined Constant Int_part => "(fun x -> int_of_float (floor x))".
Extract Inlined Constant up       => "(fun x -> (int_of_float (floor x)) + 1)".

(* real comparison deciders -> bool (sumbool is mapped to bool below) *)
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inlined Constant Rle_dec => "(fun x y -> x <= y)".
Extract Inlined Constant Rlt_dec => "(fun x y -> x < y)".

(* The classical-reals decidability axiom underlies Coq's real *construction*.
   We've mapped every real OPERATION to OCaml floats, so this is never reached
   computationally; we realize it as a (lazy) function only so the extracted
   module does not raise at load time. *)
Extract Constant sig_forall_dec => "(fun _ -> None)".

(* ---- The entry points we hand to the OCaml driver -------------------- *)
(* peaks within a bounding box; grid_encode for a chosen grid style;
   gfrom_list to build images; the grid_style constructors. *)
Extraction "speckle_core.ml"
  Image.gfrom_list
  Image.gw Image.gh
  Peaks.peaks Peaks.peaks_full
  Peaks.GSquare Peaks.GHex
  GridEncode.grid_encode.
