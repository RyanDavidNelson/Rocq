(* ===================================================================== *)
(*  Complexes.v                                                          *)
(*                                                                       *)
(*  A minimal complex-number layer over Coq's standard-library Reals.    *)
(*                                                                       *)
(*  WHY THIS FILE EXISTS / MIGRATION NOTE:                               *)
(*  The intended foundation was Coquelicot (or MathComp-analysis), which *)
(*  ships a richer complex/analysis hierarchy.  Neither could be fetched *)
(*  in the build environment used here (no opam; the opam repo and the   *)
(*  Inria/GitLab Coquelicot mirror are unreachable).  Coq's stdlib       *)
(*  [Reals] -- the very library Coquelicot is built on top of -- IS      *)
(*  available, so we use it.  All complex arithmetic the model needs is  *)
(*  confined to THIS file.  To migrate, delete the definitions below and *)
(*  `Require Export Coquelicot.Complex` (its [C], [Cplus], [Cmult],      *)
(*  [Cmod], etc. line up with the names used downstream, modulo [Cmod2]  *)
(*  = [Cmod]^2).                                                         *)
(* ===================================================================== *)

From Coq Require Import Reals List.
Import ListNotations.
Local Open Scope R_scope.

(* A complex number is a pair (real part, imaginary part). *)
Definition C : Type := (R * R)%type.

Definition Cre (z : C) : R := fst z.
Definition Cim (z : C) : R := snd z.

Definition C0 : C := (0, 0).
Definition C1 : C := (1, 0).

Definition Cadd (a b : C) : C := (Cre a + Cre b, Cim a + Cim b).
Definition Copp (a : C) : C := (- Cre a, - Cim a).
Definition Cmul (a b : C) : C :=
  (Cre a * Cre b - Cim a * Cim b, Cre a * Cim b + Cim a * Cre b).
Definition Cconj (a : C) : C := (Cre a, - Cim a).

(* e^{i theta} = (cos theta, sin theta). *)
Definition Cexp (theta : R) : C := (cos theta, sin theta).

(* Squared modulus |z|^2 = re^2 + im^2.  (This is exactly np.abs(z)**2,
   which is what the speckle generator uses, so we never need sqrt.) *)
Definition Cmod2 (z : C) : R := Cre z * Cre z + Cim z * Cim z.

(* Modulus |z| = sqrt(re^2 + im^2). *)
Definition Cmod (z : C) : R := sqrt (Cmod2 z).

(* Finite complex sum. *)
Definition Csum (l : list C) : C := fold_right Cadd C0 l.

(* A couple of sanity facts (kept light on purpose). *)
Lemma Cmod2_nonneg : forall z, (0 <= Cmod2 z)%R.
Proof.
  intros z. unfold Cmod2.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma Csum_nil : Csum [] = C0.
Proof. reflexivity. Qed.

Lemma Csum_cons : forall z l, Csum (z :: l) = Cadd z (Csum l).
Proof. reflexivity. Qed.
