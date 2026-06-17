From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlNatInt.
From Coq Require Import extraction.ExtrOcamlZInt.
From Coq Require Import ZArith Reals QArith Qreals.
From SpecklePUF Require Import Image Peaks GridEncode.

Extraction Language OCaml.

(* ---- performance fixes: kill the O(value) Peano conversions --------- *)
Extract Inlined Constant Z.of_nat        => "(fun n -> n)".
Extract Inlined Constant Pos.of_succ_nat => "(fun n -> n + 1)".
Extract Inlined Constant Z.to_nat        => "(fun n -> if n < 0 then 0 else n)".
Extract Inlined Constant Pos.to_nat      => "(fun n -> n)".

(* ---- real type + primitive ops -> OCaml double ----------------------
   Use *Extract Constant* (NOT Inlined) for the sealed-module members so
   their definitions are emitted and RbaseSymbolsImpl still satisfies its
   signature; the global R notation then resolves to float in signatures. *)
Extract Constant R       => "float".
Extract Constant R0      => "0.".
Extract Constant R1      => "1.".
Extract Constant Rplus   => "(+.)".
Extract Constant Rmult   => "( *. )".
Extract Constant Ropp    => "(fun x -> -. x)".
Extract Constant RinvImpl.Rinv => "(fun x -> 1. /. x)".
(* dead constructive bridge fields, pinned to type-correct dummies *)
Extract Constant RbaseSymbolsImpl.Rabst => "(fun _ -> 0.)".
Extract Constant RbaseSymbolsImpl.Rrepr => "(fun _ -> assert false)".

(* derived ops / library functions used by the grid geometry *)
Extract Inlined Constant Rminus  => "(-.)".
Extract Inlined Constant Rdiv    => "(/.)".
Extract Inlined Constant Rlt_dec => "(fun x y -> x < y)".
Extract Inlined Constant Rle_dec => "(fun x y -> x <= y)".
Extract Inlined Constant IZR     => "float_of_int".
Extract Inlined Constant INR     => "float_of_int".
Extract Inlined Constant Q2R     => "(fun q -> float_of_int q.qnum /. float_of_int q.qden)".
Extract Inlined Constant sqrt    => "Stdlib.sqrt".
Extract Inlined Constant cos     => "Stdlib.cos".
Extract Inlined Constant sin     => "Stdlib.sin".
Extract Inlined Constant PI      => "(4. *. Stdlib.atan 1.)".
Extract Inlined Constant Rpower  => "(fun x y -> x ** y)".
Extract Inlined Constant up      => "(fun x -> int_of_float (Stdlib.floor x) + 1)".

Extraction "Speckle_core.ml"
  peaks peaks_full grid_encode GHex GSquare.
