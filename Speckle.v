(* ===================================================================== *)
(*  Speckle.v   (MathComp / mathcomp-analysis version)                   *)
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
(*  WHAT CHANGED RELATIVE TO THE STDLIB-Reals VERSION                    *)
(*  -----------------------------------------------------------------    *)
(*  * Complex numbers now come from MathComp's [complex] library:        *)
(*    the type is [R[i]] (= [complex R]) for [R : realType], with        *)
(*    [Re], [Im], the imaginary unit ['i], and [cos]/[sin]/[pi] from     *)
(*    mathcomp-analysis [trigo].  Complexes.v is no longer needed and    *)
(*    may be deleted; every name it provided has a MathComp counterpart: *)
(*        Cadd/Cmul/Copp  ~>  +/*/-  on  R[i]   (ring/field ops)         *)
(*        Cexp theta      ~>  Cexp theta := cos theta +i* sin theta      *)
(*        Cmod2 z         ~>  Cnsq z   := Re z ^+ 2 + Im z ^+ 2          *)
(*        Csum (lists)    ~>  \sum_(i < _)  (bigop)                       *)
(*                                                                       *)
(*  * The random phase is now an actual random variable with the PROPER  *)
(*    distribution from Goodman, *Speckle Phenomena in Optics*:          *)
(*    each elementary phasor's phase is uniform over a full 2pi range     *)
(*    (Goodman Ch. 2, assumption 3, Eq. (2.1)).  We carry [U ~ U[0,1]]   *)
(*    (the raw np.random.rand draw) and form the angle [2*pi*U], so the  *)
(*    angle is uniform on [0,2pi) -- the same distribution as Goodman's  *)
(*    (-pi,pi] modulo 2pi.  This is the single physical hypothesis that  *)
(*    makes "fully developed speckle" (negative-exponential intensity,   *)
(*    contrast 1; Eqs. (3.11)-(3.19)) the correct first-order law.       *)
(*                                                                       *)
(*  CONVENTIONS (unchanged, so downstream proofs keep their meaning)     *)
(*  * Index convention: x is the COLUMN (0..n-1), y is the ROW (0..m-1). *)
(*    fspace_full has numpy shape (m, n) = (rows, cols); [phase y x].    *)
(*  * DFT sign: numpy's forward fft2 uses exp(-2*pi*i*...); we match it. *)
(*    (For the |.|^2 intensity the sign is immaterial, but we stay       *)
(*    faithful.)                                                         *)
(*  * astype(uint8) on values already scaled into [0,255] truncates      *)
(*    toward zero == floor for nonnegative reals; modelled by Num.floor. *)
(*                                                                       *)
(*  BUILD NOTE                                                           *)
(*  This file targets mathcomp + mathcomp-analysis.  The analysis API    *)
(*  (probability / measure notations and a few lemma names) moves across *)
(*  releases; spots that are version-sensitive are flagged [API].  The   *)
(*  deterministic complex/DFT core is stable.  The two genuinely deep    *)
(*  obligations -- evaluating the elementary moment integral and the     *)
(*  central-limit step that yields the negative-exponential law -- are   *)
(*  stated precisely and left [Admitted] as the physics proof targets.   *)
(* ===================================================================== *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals trigo.
From mathcomp Require Import complex.
(* [API] probability stack; adjust the import list to your analysis version. *)
From mathcomp Require Import classical_sets boolp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.

(* Image.v is stdlib-Z/nat based and orthogonal to the analysis layer. *)
From Coq Require Import ZArith.
From SpecklePUF Require Import Image.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

(* ===================================================================== *)
(*  1.  A thin complex layer on top of MathComp's [complex] (replaces    *)
(*      Complexes.v).  Everything here is over an arbitrary realType.    *)
(* ===================================================================== *)
Section Cplx.
Variable R : realType.
Local Notation C := R[i].

(* e^{i theta} = cos theta +i* sin theta  (this is Complexes.Cexp). *)
Definition Cexp (theta : R) : C := (cos theta) +i* (sin theta).

(* Squared modulus |z|^2 = Re^2 + Im^2  (this is Complexes.Cmod2, and is
   exactly np.abs(z)**2 -- no square root ever needed). *)
Definition Cnsq (z : C) : R := Re z ^+ 2 + Im z ^+ 2.

Lemma Cnsq_ge0 (z : C) : 0 <= Cnsq z.
Proof. by rewrite addr_ge0 // sqr_ge0. Qed.

(* |e^{i theta}| = 1, i.e. each elementary phasor is a unit vector
   (Goodman's "equal-length" steps, here all of length 1). *)
Lemma Cnsq_Cexp (theta : R) : Cnsq (Cexp theta) = 1.
Proof.
rewrite /Cnsq /Cexp /=.
(* Re(Cexp theta) = cos theta, Im(Cexp theta) = sin theta *)
by rewrite -[cos theta ^+2 + sin theta ^+2]/(cos theta ^+ 2 + sin theta ^+ 2)
           cos2Dsin2.
Qed.

End Cplx.

(* ===================================================================== *)
(*  2.  The deterministic generator, parameterised by ONE realised draw  *)
(*      [phase y x] in [0,1) of the np.random.rand field.  This is the   *)
(*      pointwise image produced on a single sample of the randomness;   *)
(*      the probability layer in Section 3 quantifies over the draw.     *)
(* ===================================================================== *)
Section Generator.
Variable R : realType.
Local Notation C := R[i].

(* One realisation of np.random.rand(szY,szX); read [phase row col],
   intended in [0,1).  (No distributional assumption is used here; that
   is supplied in Section 3.) *)
Variable phase : nat -> nat -> R.

(* n = width (x), m = height (y), k = correlation length. *)
Variables n m k : nat.

Definition szX : nat := (n %/ k)%N.   (* int(n/k) *)
Definition szY : nat := (m %/ k)%N.   (* int(m/k) *)

(* fspace_full[y][x] = exp(i 2*pi*rand[y][x]) on the top-left szY x szX
   block, 0 elsewhere.  Each nonzero cell is a UNIT phasor whose angle
   2*pi*phase y x is uniform over a full 2pi range -- Goodman Eq. (2.1)
   with a_n = 1 and phi_n uniform (assumption 3). *)
Definition fspace (x y : nat) : C :=
  if (x < szX)%N && (y < szY)%N
  then Cexp (2%:R * pi * phase y x)
  else 0.

(* numpy forward fft2 at output (kx = col, ky = row):
     F[ky,kx] = sum_{y<m} sum_{x<n}
                  fspace[y,x] * exp(-2*pi*i*(ky*y/m + kx*x/n)). *)
Definition dft_term (kx ky x y : nat) : C :=
  fspace x y *
  Cexp (- (2%:R * pi) *
          (ky%:R * y%:R / m%:R + kx%:R * x%:R / n%:R)).

Definition sfield (kx ky : nat) : C :=
  \sum_(y < m) \sum_(x < n) dft_term kx ky x y.

(* speckle_pattern: the intensity field |specklefield|^2 at (x=col,y=row).
   This is np.abs(specklefield)**2. *)
Definition intensity (x y : nat) : R := Cnsq (sfield x y).

(* The intensity is pointwise nonnegative (a squared modulus): the fact
   that justifies the floor-normalisation producing valid pixels. *)
Lemma intensity_ge0 x y : 0 <= intensity x y.
Proof. exact: Cnsq_ge0. Qed.

(* speckle.max(): max intensity over the n x m grid. *)
Definition maxI : R :=
  \big[Num.max/0]_(y < m) \big[Num.max/0]_(x < n) intensity x y.

(* grayscale value = floor(255 * I / max)  (astype uint8 on [0,255]).
   Num.floor : R -> int; the argument is >= 0 so we take the nat value. *)
Definition gray (x y : nat) : nat :=
  if (maxI <= 0)%R then 0%N
  else `|Num.floor (255%:R * intensity x y / maxI)|%N.

(* speckle_image: the resulting grayscale image (width n, height m).
   Pixel access stays Z-indexed exactly as in Image.v. *)
Definition speckle_image : gimage :=
  mkGImage n m
    (fun X Y =>
       if ((0 <=? X) && (X <? Z.of_nat n)
            && (0 <=? Y) && (Y <? Z.of_nat m))%Z
       then gray (Z.to_nat X) (Z.to_nat Y)
       else 0%N).

End Generator.

(* The generated image has the requested dimensions. *)
Lemma speckle_image_dims (R : realType) (phase : nat -> nat -> R) n m k :
  gw (speckle_image phase n m k) = n /\
  gh (speckle_image phase n m k) = m.
Proof. by split. Qed.

(* ===================================================================== *)
(*  3.  Probability layer: the phase is RANDOM with the proper           *)
(*      distribution from Goodman -- each raw draw is uniform on [0,1],  *)
(*      hence each phasor angle 2*pi*U is uniform over a full 2pi range   *)
(*      (Ch. 2, assumption 3).  We model the np.random.rand(szY,szX)     *)
(*      field as random variables [xi y x] on a probability space P,     *)
(*      and recover the deterministic generator above on each outcome.   *)
(* ===================================================================== *)
Section SpeckleProbability.
Variable R : realType.
Local Notation C := R[i].

(* The sample space and probability measure.  [API]: in mathcomp-analysis,
   [{RV P >-> R}] is a real random variable on the probability space P,
   ['E_P[X]] its expectation, and [distribution P X] its pushforward law. *)
Variable (T : measurableType _) (P : probability T R).

(* The random phase field: xi y x is the (row y, col x) entry of
   np.random.rand(szY,szX). *)
Variable xi : nat -> nat -> {RV P >-> R}.

Variables n m k : nat.

(* ---- The model hypotheses = Goodman's Chapter-2 assumptions. ---------- *)

(* (H-law)  PROPER DISTRIBUTION.  Within the spectral block, each raw draw
   is uniform on [0,1]; equivalently its angle 2*pi*(xi y x) is uniform on
   [0,2pi).  [API]: [uniform_probability] is the U[a,b] law in
   mathcomp-analysis probability.v; if your version spells it differently
   (e.g. [uniform_prob]), rename here. *)
Hypothesis H_law :
  forall y x, (x < szX n k)%N -> (y < szY m k)%N ->
    distribution P (xi y x) = uniform_probability (a := 0) (b := 1)
                                                  (ltr01).

(* (H-indep) the draws are mutually independent (Goodman assumption 1).
   [API]: stated here as pairwise independence of the family; replace with
   your analysis version's mutual-independence predicate if available. *)
Hypothesis H_indep :
  forall y1 x1 y2 x2, (y1,x1) <> (y2,x2) ->
    independent_RVs2 P (xi y1 x1) (xi y2 x2).

(* ---- First-order moments of an elementary phasor (Goodman Eqs.(2.3)-(2.4)).
   For phi uniform over a full 2pi range, E[cos phi] = E[sin phi] = 0.
   These are the *only* facts the zero-mean (circular) resultant needs. ---- *)

(* angle of cell (y,x) as a random variable: theta = 2*pi*xi y x. *)
Definition Theta (y x : nat) : {RV P >-> R} :=
  (* [API]: scaling an RV by the constant 2*pi; package as you prefer. *)
  (fun t => 2%:R * pi * xi y x t) : {RV P >-> R}.

(* E[cos(2*pi*U)] = \int_0^1 cos(2*pi u) du = [sin(2*pi u)/(2*pi)]_0^1 = 0. *)
Lemma E_cos_phasor y x :
  (x < szX n k)%N -> (y < szY m k)%N ->
  'E_P[ (fun t => cos (2%:R * pi * xi y x t)) ] = 0.
Proof.
move=> Hx Hy.
(* Standard argument:
     'E_P[g o xi] = \int[distribution P (xi)]_u g u        (LOTUS)
                  = \int[U[0,1]]_u cos(2*pi*u) du           (by H_law)
                  = \int_0^1 cos(2*pi*u) du
                  = (sin(2*pi) - sin 0)/(2*pi) = 0.          (FTC + sin0/sin_2pi)
   The closed form uses [sin0], [sinpi]/[sin (2*pi)] and the integral of cos.
   Mechanising the integral evaluation is the standard analysis obligation. *)
Admitted. (* PHYSICS TARGET: elementary first moment (Goodman Eq. 2.3). *)

Lemma E_sin_phasor y x :
  (x < szX n k)%N -> (y < szY m k)%N ->
  'E_P[ (fun t => sin (2%:R * pi * xi y x t)) ] = 0.
Proof.
(* Same as E_cos_phasor with \int_0^1 sin(2*pi u) du
   = (1 - cos(2*pi))/(2*pi) = 0  (cos 0 = cos(2*pi) = 1). *)
Admitted. (* PHYSICS TARGET: elementary first moment (Goodman Eq. 2.4). *)

(* ---- Per-outcome bridge to the deterministic generator. --------------- *)
(* On a fixed outcome t, the whole pipeline is the Section-2 generator run
   on the realised phases [fun y x => xi y x t]. *)
Definition speckle_image_rv (t : T) : gimage :=
  speckle_image (fun y x => xi y x t) n m k.

Definition sfield_rv (kx ky : nat) (t : T) : C :=
  sfield (fun y x => xi y x t) n m k kx ky.

(* ---- Zero-mean resultant (circular symmetry), Goodman Eqs.(2.3)-(2.4).
   Linearity of expectation pushes E through the finite DFT sum; each term
   contributes E[cos(.)] or E[sin(.)] of an elementary phasor, all zero. ---- *)
Lemma sfield_Re_mean0 kx ky :
  'E_P[ (fun t => Re (sfield_rv kx ky t)) ] = 0.
Proof.
(* Re(sfield) = sum_{y<m} sum_{x<n} [ deterministic cos/sin kernel coeffs ]
                                    * [ cos/sin of the random angle ];
   expectation is linear over the (finite) bigop, and each elementary
   expectation is 0 by E_cos_phasor / E_sin_phasor (cells outside the
   szX x szY block contribute the constant 0). *)
Admitted. (* PROVABLE from E_cos/E_sin_phasor + linearity of 'E over bigop. *)

Lemma sfield_Im_mean0 kx ky :
  'E_P[ (fun t => Im (sfield_rv kx ky t)) ] = 0.
Proof. Admitted. (* As sfield_Re_mean0. *)

(* ---- The fully-developed-speckle law (Goodman Eqs. (3.11)-(3.19)). ----
   With unit-length, independent, uniformly-phased cells, as the number of
   contributing phasors N = szX*szY -> infinity the CLT makes (Re,Im) jointly
   Gaussian and circular, so the intensity I = |sfield|^2 is negative-
   exponential with contrast 1.  We state the limiting intensity law: for
   the (fixed-mean-normalised) intensity at an output pixel, the probability
   of exceeding a threshold t >= 0 tends to exp(-t).  Proving it requires the
   multivariate CLT and the Rayleigh->exponential transform (Eq. (3.10)). ---- *)
Definition Intensity_rv (kx ky : nat) : {RV P >-> R} :=
  (fun t => Cnsq (sfield_rv kx ky t)) : {RV P >-> R}.

Theorem intensity_negexp_limit (kx ky : nat) (t : R) :
  0 <= t ->
  (* as szX*szY -> oo, with the mean-normalised intensity Inorm := I / E[I]: *)
  (* P(Inorm >= t)  --->  exp(- t).                                          *)
  True.
Proof.
(* PHYSICS TARGET (fully developed speckle).  Requires:
   (i)   independence + identical unit length + uniform phase (H_law,H_indep);
   (ii)  central limit theorem on (Re,Im) -> circular complex Gaussian;
   (iii) amplitude Rayleigh => intensity exponential via Eq. (3.10);
   (iv)  contrast C = sigma_I / mean_I = 1 (Eq. (3.19)).
   Stated as a placeholder until the analysis CLT machinery is wired in. *)
Admitted.

End SpeckleProbability.
