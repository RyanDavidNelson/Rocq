(* ===================================================================== *)
(*  Speckle.v   (MathComp real_closed [complex] version)                 *)
(*                                                                       *)
(*  Faithful model of the generator from the email:                     *)
(*                                                                       *)
(*    def speckle_pattern(n, m, k):                                      *)
(*        szX = int(n/k); szY = int(m/k)                                 *)
(*        fourier_spectrum = np.exp(1j*2*np.pi*np.random.rand(szY,szX))  *)
(*        fspace_full = np.zeros((m,n), dtype=complex)                   *)
(*        fspace_full[0:szY,0:szX] += fourier_spectrum                   *)
(*        specklefield = fft2(fspace_full)                               *)
(*        speckelIntensity = np.abs(specklefield)**2                     *)
(*        return speckelIntensity                                        *)
(*    def speckle_image(n, m, k):                                        *)
(*        speckle = speckle_pattern(n, m, k)                             *)
(*        scale = 1/(speckle.max()/255)                                  *)
(*        grayscale = (scale*speckle).astype(np.uint8)                   *)
(*        return Image.fromarray(grayscale)                              *)
(*                                                                       *)
(*  DESIGN OF THIS FILE                                                  *)
(*  ----------------------------------------------------------------     *)
(*  We separate two concerns and re-prove NOTHING that Goodman or        *)
(*  standard analysis already establishes:                               *)
(*                                                                       *)
(*   (A) The DETERMINISTIC generator -- the complex DFT and the          *)
(*       intensity |.|^2 -- is built concretely on MathComp's complex    *)
(*       numbers [R[i]] (= [complex R], from rocq-mathcomp-real-closed). *)
(*       The only facts proved here are the cheap structural ones we     *)
(*       actually need to TIE the generator to the physics:              *)
(*         - each active spectral cell is a UNIT phasor;                 *)
(*         - the speckle field at any output pixel is exactly a SUM of   *)
(*           [szX*szY] unit phasors (Goodman's random-phasor sum).       *)
(*                                                                       *)
(*   (B) The PHYSICS is axiomatized as Goodman's theorem (Ch. 3,         *)
(*       first-order statistics): a sum of independent unit phasors with *)
(*       phases uniform over a full 2*pi range has, in the large-N       *)
(*       regime, a negative-exponential intensity with contrast 1 --     *)
(*       the DEFINITION of fully developed speckle.  We do not re-derive  *)
(*       the central-limit / Rayleigh->exponential chain; it enters as a *)
(*       single named hypothesis [Goodman_first_order].                  *)
(*                                                                       *)
(*  The final result [speckle_fully_developed] then TIES (A) to (B):     *)
(*  the generator's per-pixel intensity is fully developed speckle.      *)
(*                                                                       *)
(*  WHAT REPLACED Complexes.v                                            *)
(*  ----------------------------------------------------------------     *)
(*  Complexes.v (stdlib-Reals pairs) is no longer used by anything and   *)
(*  may be deleted.  Its names map to MathComp as:                       *)
(*        C               ~>  R[i]   (= complex R)                       *)
(*        Cadd/Cmul/Copp  ~>  + / * / -   (ring ops on R[i])             *)
(*        Cexp theta      ~>  Cexp theta := cos theta +i* sin theta      *)
(*        Cmod2 z         ~>  Cnsq z   := Re z ^+ 2 + Im z ^+ 2          *)
(*        Csum (lists)    ~>  \sum_(i < _)   (bigop on the zmodType)     *)
(*  with [cos]/[sin]/[pi] now from mathcomp-analysis [trigo].            *)
(*                                                                       *)
(*  CONVENTIONS (unchanged)                                              *)
(*  * Index convention: x is the COLUMN (0..n-1), y is the ROW (0..m-1). *)
(*    fspace has numpy shape (m,n) = (rows,cols); phases read [phase y x].*)
(*  * DFT sign: numpy's forward fft2 uses exp(-2*pi*i*...); we match it.  *)
(*    (For |.|^2 the sign is immaterial, but we stay faithful.)          *)
(*  * astype(uint8) on values already in [0,255] truncates toward zero   *)
(*    == floor for nonnegative reals; modelled by Num.floor.            *)
(*                                                                       *)
(*  BUILD NOTE                                                           *)
(*  Requires: rocq-mathcomp-{boot,algebra,field,reals}, mathcomp-analysis*)
(*  (trigo, exp) and rocq-mathcomp-real-closed (complex).  Install the   *)
(*  last with:  opam install rocq-mathcomp-real-closed                   *)
(*  No measure-theory / probability imports are needed: the statistical  *)
(*  layer is abstract (an expectation [Exp] and a probability [Pr]),     *)
(*  which keeps the file independent of the fast-moving analysis         *)
(*  probability API.  Any concrete probability space instantiates it.    *)
(* ===================================================================== *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals trigo exp.
From mathcomp Require Import complex.

From Coq Require Import ZArith.
From SpecklePUF Require Import Image.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

(* ===================================================================== *)
(*  1.  Thin complex layer on top of MathComp's [complex] (replaces      *)
(*      Complexes.v).  Everything is over an arbitrary [realType].       *)
(* ===================================================================== *)
Section Cplx.
Variable R : realType.
Local Notation C := R[i].

(* e^{i theta} = cos theta +i* sin theta. *)
Definition Cexp (theta : R) : C := (cos theta) +i* (sin theta).

(* Squared modulus |z|^2 = Re^2 + Im^2.  This is exactly np.abs(z)**2:
   no square root is ever needed. *)
Definition Cnsq (z : C) : R := Re z ^+ 2 + Im z ^+ 2.

Lemma Cnsq_ge0 (z : C) : 0 <= Cnsq z.
Proof. rewrite /Cnsq; exact: addr_ge0 (sqr_ge0 _) (sqr_ge0 _). Qed.

(* |e^{i theta}|^2 = 1: each elementary phasor is a UNIT vector
   (Goodman's equal-length steps, here all of length 1). *)
Lemma Cnsq_Cexp (theta : R) : Cnsq (Cexp theta) = 1.
Proof. by rewrite /Cnsq /Cexp /= cos2Dsin2. Qed.

(* Phasor addition law (de Moivre): e^{ia} e^{ib} = e^{i(a+b)}.
   This is textbook complex algebra (cosD/sinD); per the request not to
   re-prove standard mathematics it is taken as an axiom.  To prove it
   instead, use real_closed's [simpc] together with [cosD] and [sinD]. *)
Axiom CexpD : forall a b : R, Cexp a * Cexp b = Cexp (a + b).

End Cplx.

(* ===================================================================== *)
(*  2.  The deterministic generator, parameterised by ONE realised draw  *)
(*      [phase y x] in [0,1) of np.random.rand.  This is the pointwise   *)
(*      image produced on a single sample; Section 3 quantifies over the *)
(*      draw.  (All arguments are explicit for predictable downstream    *)
(*      use.)                                                             *)
(* ===================================================================== *)
Section Generator.
Variable R : realType.
Local Notation C := R[i].

(* n = width (x), m = height (y), k = correlation length. *)
Definition szX (n k : nat) : nat := (n %/ k)%N.   (* int(n/k) *)
Definition szY (m k : nat) : nat := (m %/ k)%N.   (* int(m/k) *)

(* The top-left szY x szX spectral block is "active". *)
Definition active (n m k x y : nat) : bool :=
  (x < szX n k)%N && (y < szY m k)%N.

(* fspace[y][x] = exp(i 2*pi*rand[y][x]) on the active block, 0 elsewhere.
   Each active cell is a UNIT phasor whose angle 2*pi*(phase y x) is
   uniform over a full 2*pi range -- Goodman Ch. 2, assumption 3. *)
Definition fspace (phase : nat -> nat -> R) (n m k x y : nat) : C :=
  if active n m k x y then Cexp (2%:R * pi * phase y x) else 0.

(* The deterministic DFT phase carried by output (kx=col, ky=row) at
   input (x,y): numpy's forward fft2 uses exp(-2*pi*i*(ky*y/m + kx*x/n)). *)
Definition dft_phase (n m kx ky x y : nat) : R :=
  - (2%:R * pi) * (ky%:R * y%:R / m%:R + kx%:R * x%:R / n%:R).

(* Total angle of an ACTIVE cell's contribution to output (kx,ky):
   the random phasor angle plus the deterministic DFT phase. *)
Definition cell_angle (phase : nat -> nat -> R)
                      (n m kx ky x y : nat) : R :=
  2%:R * pi * phase y x + dft_phase n m kx ky x y.

(* One term of the DFT sum. *)
Definition dft_term (phase : nat -> nat -> R)
                    (n m k kx ky x y : nat) : C :=
  fspace phase n m k x y * Cexp (dft_phase n m kx ky x y).

(* specklefield[ky,kx] = sum_{y<m} sum_{x<n} dft_term. *)
Definition sfield (phase : nat -> nat -> R)
                  (n m k kx ky : nat) : C :=
  \sum_(y < m) \sum_(x < n) dft_term phase n m k kx ky x y.

(* speckle_pattern: intensity |specklefield|^2 at (x=col,y=row). *)
Definition intensity (phase : nat -> nat -> R)
                     (n m k x y : nat) : R :=
  Cnsq (sfield phase n m k x y).

Lemma intensity_ge0 phase n m k x y : 0 <= intensity phase n m k x y.
Proof. exact: Cnsq_ge0. Qed.

(* ---- Structural bridge to Goodman's random-phasor sum. --------------- *)
(* Each ACTIVE term is a single unit phasor e^{i (cell_angle)}; inactive
   terms are 0.  (Uses the phasor addition law CexpD.) *)
Lemma dft_term_E phase n m k kx ky x y :
  dft_term phase n m k kx ky x y
    = (if active n m k x y
       then Cexp (cell_angle phase n m kx ky x y) else 0).
Proof.
rewrite /dft_term /fspace /cell_angle.
by case: (active n m k x y); [rewrite CexpD | rewrite mul0r].
Qed.

(* Hence the speckle field at any output pixel is exactly the sum, over
   the active block, of unit phasors -- precisely Goodman's resultant. *)
Lemma sfield_E phase n m k kx ky :
  sfield phase n m k kx ky
    = \sum_(y < m) \sum_(x < n)
        (if active n m k x y
         then Cexp (cell_angle phase n m kx ky x y) else 0).
Proof.
by apply: eq_bigr => y _; apply: eq_bigr => x _; rewrite dft_term_E.
Qed.

(* speckle.max(): max intensity over the n x m grid. *)
Definition maxI (phase : nat -> nat -> R) (n m k : nat) : R :=
  \big[Num.max/0]_(y < m) \big[Num.max/0]_(x < n) intensity phase n m k x y.

(* grayscale value = floor(255 * I / max)  (astype uint8 on [0,255]). *)
Definition gray (phase : nat -> nat -> R) (n m k x y : nat) : nat :=
  if (maxI phase n m k <= 0)%R then 0%N
  else `|Num.floor (255%:R * intensity phase n m k x y
                          / maxI phase n m k)|%N.

(* speckle_image: grayscale image (width n, height m); Z-indexed pixels. *)
Definition speckle_image (phase : nat -> nat -> R) (n m k : nat) : gimage :=
  mkGImage n m
    (fun X Y =>
       if ((0 <=? X) && (X <? Z.of_nat n)
            && (0 <=? Y) && (Y <? Z.of_nat m))%Z
       then gray phase n m k (Z.to_nat X) (Z.to_nat Y)
       else 0%N).

End Generator.

(* The generated image has the requested dimensions. *)
Lemma speckle_image_dims (R : realType) (phase : nat -> nat -> R) n m k :
  gw (speckle_image phase n m k) = n /\
  gh (speckle_image phase n m k) = m.
Proof. by split. Qed.

(* ===================================================================== *)
(*  3.  The physics layer: "fully developed speckle" and Goodman's       *)
(*      first-order theorem (Ch. 3), tied to the generator.              *)
(*                                                                       *)
(*  We DO NOT build a measure-theoretic probability space.  The only     *)
(*  statistical primitives we need are an expectation [Exp] and a        *)
(*  probability [Pr] of an event over the random phase field; any        *)
(*  concrete probability space supplies them.  Goodman's CLT/Rayleigh    *)
(*  derivation enters as the single hypothesis [Goodman_first_order].    *)
(* ===================================================================== *)
Section FullyDeveloped.
Variable R : realType.
Local Notation C := R[i].

(* An outcome is a realised raw phase field: [om y x] in [0,1) is the
   np.random.rand draw at row y, column x. *)
Definition outcome := nat -> nat -> R.

(* Abstract statistical primitives over the random phase field. *)
Variable Pr  : (outcome -> Prop) -> R.   (* probability of an event   *)
Variable Exp : (outcome -> R)    -> R.   (* expectation of an observable *)

(* The law of a real, nonnegative observable, recorded by its mean and
   its survival function  t |-> P(X > t). *)
Record speckle_law := SpeckleLaw { sl_mean : R; sl_surv : R -> R }.

Definition law_of (X : outcome -> R) : speckle_law :=
  SpeckleLaw (Exp X) (fun t => Pr (fun om => t < X om)).

(* FULLY DEVELOPED SPECKLE (Goodman, Ch. 3, first-order statistics):
   the intensity is negative-exponential, contrast C = sigma_I/Ibar = 1,
   i.e. mean Ibar > 0 and survival  P(I > t) = exp(-t/Ibar)  for t >= 0.
   (Contrast 1 is automatic for the negative-exponential law and is the
   defining property of fully developed speckle; Goodman Eqs. for p_I and
   the contrast result.) *)
Definition fully_developed (L : speckle_law) : Prop :=
  (0 < sl_mean L) /\
  (forall t : R, 0 <= t -> sl_surv L t = expR (- t / sl_mean L)).

(* ---- Fix image parameters and an output pixel (kx,ky). --------------- *)
Variables n m k : nat.
Variables kx ky : nat.

(* The random speckle field / intensity at the chosen pixel, as functions
   of the raw draw [om] (Section 2's generator run on each outcome). *)
Definition field_rv : outcome -> C := fun om => sfield om n m k kx ky.
Definition intensity_rv : outcome -> R := fun om => intensity om n m k kx ky.

(* Number of contributing (active) elementary phasors. *)
Definition Nphasors : nat := (szX n k * szY m k)%N.

Lemma Nphasors_gt0 :
  (0 < szX n k)%N -> (0 < szY m k)%N -> (1 <= Nphasors)%N.
Proof. by move=> hx hy; rewrite /Nphasors muln_gt0 hx hy. Qed.

(* ---- The single physical hypothesis on the draws. -------------------- *)
(* [iid_unif_phase angle] : the family of active-cell phases [angle y x]
   is statistically independent, each uniform over a full 2*pi range.
   This is exactly what np.random.rand provides: each raw draw is
   independent and U[0,1), so its angle 2*pi*(draw) is uniform on [0,2pi);
   adding the deterministic per-cell DFT phase is a constant rotation,
   which leaves a uniform-on-the-circle phase uniform and independent
   (Goodman Ch. 2, assumptions 1-3).  Kept abstract; the instance below
   records that the generator's [cell_angle] family is such a field. *)
Variable iid_unif_phase : (nat -> nat -> outcome -> R) -> Prop.

Hypothesis H_phase_model :
  iid_unif_phase (fun y x om => cell_angle om n m kx ky x y).

(* ---- Goodman's first-order speckle theorem (AXIOMATIZED PHYSICS). ----
   If a field S is the sum, over the active block, of UNIT phasors whose
   phases are independent and uniform over a full 2*pi range, then -- in
   the large-N regime, which we adopt as the idealized definition of
   "fully developed" (Goodman 3.2.1) -- its intensity |S|^2 is fully
   developed speckle.  This packages the CLT on (Re,Im) -> circular
   complex Gaussian and the Rayleigh -> negative-exponential transform;
   we do not re-derive it here. *)
Hypothesis Goodman_first_order :
  forall (angle : nat -> nat -> outcome -> R) (S : outcome -> C),
    (1 <= Nphasors)%N ->
    iid_unif_phase angle ->
    (forall om, S om =
       \sum_(y < m) \sum_(x < n)
         (if active n m k x y then Cexp (angle y x om) else 0)) ->
    fully_developed (law_of (fun om => Cnsq (S om))).

(* ---- The tie: the generator produces fully developed speckle. -------- *)
Theorem speckle_fully_developed :
  (1 <= Nphasors)%N ->
  fully_developed (law_of intensity_rv).
Proof.
move=> hN.
(* The field at this pixel is a sum of Nphasors unit phasors (sfield_E). *)
have hsum : forall om,
  field_rv om =
    \sum_(y < m) \sum_(x < n)
      (if active n m k x y
       then Cexp (cell_angle om n m kx ky x y) else 0).
  by move=> om; rewrite /field_rv; exact: sfield_E.
(* Apply Goodman's theorem to that resultant; the conclusion is the law of
   [fun om => Cnsq (field_rv om)], which is definitionally [intensity_rv]. *)
exact: (Goodman_first_order
          (fun y x om => cell_angle om n m kx ky x y)
          field_rv hN H_phase_model hsum).
Qed.

End FullyDeveloped.
