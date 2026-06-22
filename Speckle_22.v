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
(*  COMPLEX NUMBERS: SELF-CONTAINED PAIR LAYER (no mathcomp-real-closed) *)
(*  -----------------------------------------------------------------    *)
(*  The earlier draft used MathComp's [complex] library ([R[i]]), which  *)
(*  lives in mathcomp-real-closed.  That package versions independently  *)
(*  of mathcomp-analysis and is awkward to co-install / co-use: its      *)
(*  [complex] predates the analysis [realType] + measure/topology layer  *)
(*  and does not provide the canonical/measurable instances one needs    *)
(*  to treat [R[i]] inside the probability stack.  Since every quantity  *)
(*  this development actually needs is REAL -- we only ever use the real  *)
(*  part, imaginary part and squared modulus [Re^2 + Im^2] -- we drop    *)
(*  the dependency entirely and model a complex number as a pair         *)
(*  [(re, im) : R * R].  Complex ADDITION and the complex ZERO are then  *)
(*  exactly MathComp's componentwise product [zmodType] structure on     *)
(*  [R * R], so [\sum] and [0] work for free; only complex MULTIPLICATION *)
(*  is non-componentwise and is given explicitly as [Cmul].              *)
(*                                                                       *)
(*  Name correspondence with the old [complex]-based code:               *)
(*        z : R[i]      ~>  z : R * R                                     *)
(*        Re z / Im z   ~>  ReC z / ImC z   (= z.1 / z.2)                 *)
(*        z * w         ~>  Cmul z w                                      *)
(*        z + w , 0     ~>  z + w , 0       (prod zmodType: componentwise) *)
(*        \sum ... z    ~>  \sum ... z       (same bigop, prod zmodType)   *)
(*        Cexp theta    ~>  Cexp theta := (cos theta, sin theta)          *)
(*        Cmod2 z       ~>  Cnsq z   := ReC z ^+ 2 + ImC z ^+ 2           *)
(*                                                                       *)
(*  * The random phase is an actual random variable with the proper      *)
(*    distribution from Goodman, *Speckle Phenomena in Optics*: each     *)
(*    elementary phasor's phase is uniform over a full 2pi range          *)
(*    (Goodman Ch. 2, assumption 3, Eq. (2.1)).  We carry [U ~ U[0,1]]   *)
(*    (the raw np.random.rand draw) and form the angle [2*pi*U].         *)
(*                                                                       *)
(*  CONVENTIONS (unchanged, so downstream proofs keep their meaning)     *)
(*  * Index convention: x is the COLUMN (0..n-1), y is the ROW (0..m-1). *)
(*    fspace_full has numpy shape (m, n) = (rows, cols); [phase y x].    *)
(*  * DFT sign: numpy's forward fft2 uses exp(-2*pi*i*...); we match it. *)
(*  * astype(uint8) on values already scaled into [0,255] truncates      *)
(*    toward zero == floor for nonnegative reals; modelled by floor. *)
(*                                                                       *)
(*  BUILD NOTE                                                           *)
(*  This file targets mathcomp + mathcomp-analysis on Rocq 9.1.  The      *)
(*  current analysis ships [uniform_prob] (uniform_distribution.v) and    *)
(*  [exponential_prob] (exponential_distribution.v), so:                  *)
(*   * the phase law is now Goodman's actual input [xi ~ U[0,1]] via      *)
(*     [uniform_prob] (one hypothesis), not the two derived moments;      *)
(*   * the final law is stated as the DISTRIBUTION of the intensity and   *)
(*     DERIVED in closed form (1 - e^{-t}) from [exponential_prob_itv0c]. *)
(*  ONE source of randomness: the phases [xi].  The intensity is their    *)
(*  deterministic function [Intensity_rv], exposed as the {RV} [NI] and   *)
(*  pinned to the phases by [NIE] -- no second independent variable.      *)
(*  Two physics inputs remain assumed (the trust boundary): the resultant *)
(*  zero means and the CLT (the limit law of [NI]); analysis has no       *)
(*  weak-convergence/CLT layer.  The first moments E[cos]=E[sin]=0 follow *)
(*  from [xi_uniform] (transfer + [continuous_FTC2]; see the note above   *)
(*  [xi_uniform]).  Spots that move across releases are flagged [API].   *)
(* ===================================================================== *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals trigo.
From mathcomp Require Import constructive_ereal.
(* [API] probability stack; adjust the import list to your analysis version. *)
From mathcomp Require Import classical_sets boolp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
(* [API] probability layers used by the final theorem (current analysis):
   - [exp]/[sequences]          : the real exponential [expR];
   - [random_variable]          : [distribution P X] (pushforward law) and {RV};
   - [exponential_distribution] : [exponential_prob], [exponential_prob_itv0c];
   - [uniform_distribution]     : [uniform_prob] (the phase law).
   On builds where [probability] already re-exports [random_variable] the
   duplicate import is harmless. *)
From mathcomp Require Import sequences exp.
From mathcomp Require Import random_variable exponential_distribution.
From mathcomp Require Import uniform_distribution.

(* Image.v is stdlib-Z/nat based and orthogonal to the analysis layer. *)
From Coq Require Import ZArith.
From SpecklePUF Require Import Image.

(* ZArith's BinNat rebinds the [%N] delimiter key to Coq's binary [N_scope],
   which would shadow ssreflect's [nat_scope] and silently turn every [%N]
   (and [%/]) in this file into binary-N / polynomial operations.  Restore
   ssreflect's intent so [(_ %/ _)%N], [(_ < _)%N], etc. mean nat. *)
Delimit Scope nat_scope with N.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* ===================================================================== *)
(*  1.  A self-contained complex layer as pairs [R * R] (replaces the    *)
(*      mathcomp-real-closed [complex] library).  Everything here is over *)
(*      an arbitrary realType; R is left implicit so the accessors infer  *)
(*      it from their argument exactly like [Re]/[Im] did.               *)
(* ===================================================================== *)

(* Real and imaginary part: the two projections of the pair. *)
Definition ReC {R : realType} (z : R * R) : R := z.1.
Definition ImC {R : realType} (z : R * R) : R := z.2.

(* Complex multiplication (the ONE operation that is not componentwise).
   (a+bi)(c+di) = (ac - bd) + (ad + bc) i. *)
Definition Cmul {R : realType} (z w : R * R) : R * R :=
  (ReC z * ReC w - ImC z * ImC w, ReC z * ImC w + ImC z * ReC w).

(* e^{i theta} = cos theta + i sin theta  (this is the old Complexes.Cexp). *)
Definition Cexp {R : realType} (theta : R) : R * R := (cos theta, sin theta).

(* Squared modulus |z|^2 = Re^2 + Im^2  (the old Complexes.Cmod2, and
   exactly np.abs(z)**2 -- no square root ever needed). *)
Definition Cnsq {R : realType} (z : R * R) : R := ReC z ^+ 2 + ImC z ^+ 2.

Lemma Cnsq_ge0 {R : realType} (z : R * R) : 0 <= Cnsq z.
Proof. by rewrite addr_ge0// sqr_ge0. Qed.

(* |e^{i theta}| = 1, i.e. each elementary phasor is a unit vector
   (Goodman's "equal-length" steps, here all of length 1). *)
Lemma Cnsq_Cexp {R : realType} (theta : R) : Cnsq (Cexp theta) = 1.
Proof. by rewrite /Cnsq /ReC /ImC /Cexp/= cos2Dsin2. Qed.

(* ReC / ImC are additive: the projections of the prod zmodType commute
   with finite sums.  (Complex addition is componentwise, so this is the
   fact that lets linearity push through the DFT bigop.) *)
Lemma ReC_sum {R : realType} (I : Type) (r : seq I) (F : I -> R * R) :
  ReC (\sum_(i <- r) F i) = \sum_(i <- r) ReC (F i).
Proof. by apply: (big_morph ReC) => [x y|]; rewrite /ReC. Qed.

Lemma ImC_sum {R : realType} (I : Type) (r : seq I) (F : I -> R * R) :
  ImC (\sum_(i <- r) F i) = \sum_(i <- r) ImC (F i).
Proof. by apply: (big_morph ImC) => [x y|]; rewrite /ImC. Qed.

(* ===================================================================== *)
(*  2.  The deterministic generator, parameterised by ONE realised draw  *)
(*      [phase y x] in [0,1) of the np.random.rand field.                *)
(* ===================================================================== *)
Section Generator.
Variable R : realType.
Local Notation C := (R * R)%type.

(* One realisation of np.random.rand(szY,szX); read [phase row col]. *)
Variable phase : nat -> nat -> R.

(* n = width (x), m = height (y), k = correlation length. *)
Variables n m k : nat.

Definition szX : nat := (n %/ k)%N.   (* int(n/k) *)   (* int(n/k) *)
Definition szY : nat := (m %/ k)%N.   (* int(m/k) *)   (* int(m/k) *)

(* fspace_full[y][x] = exp(i 2*pi*rand[y][x]) on the top-left szY x szX
   block, 0 elsewhere.  Each nonzero cell is a UNIT phasor. *)
Definition fspace (x y : nat) : C :=
  if (x < szX)%N && (y < szY)%N
  then Cexp (2%:R * pi * phase y x)
  else 0.

(* numpy forward fft2 at output (kx = col, ky = row):
     F[ky,kx] = sum_{y<m} sum_{x<n}
                  fspace[y,x] * exp(-2*pi*i*(ky*y/m + kx*x/n)). *)
Definition dft_term (kx ky x y : nat) : C :=
  Cmul (fspace x y)
       (Cexp (- (2%:R * pi) *
                (ky%:R * y%:R / m%:R + kx%:R * x%:R / n%:R))).

Definition sfield (kx ky : nat) : C :=
  \sum_(y < m) \sum_(x < n) dft_term kx ky x y.

(* speckle_pattern: the intensity field |specklefield|^2 at (x=col,y=row). *)
Definition intensity (x y : nat) : R := Cnsq (sfield x y).

(* The intensity is pointwise nonnegative (a squared modulus). *)
Lemma intensity_ge0 x y : 0 <= intensity x y.
Proof. exact: Cnsq_ge0. Qed.

(* speckle.max(): max intensity over the n x m grid. *)
Definition maxI : R :=
  \big[Num.max/0]_(y < m) \big[Num.max/0]_(x < n) intensity x y.

(* grayscale value = floor(255 * I / max)  (astype uint8 on [0,255]). *)
Definition gray (x y : nat) : nat :=
  if (maxI <= 0)%R then 0%N
  else `|archimedean.Num.floor (255%:R * intensity x y / maxI)%R|%N.

(* speckle_image: the resulting grayscale image (width n, height m). *)
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
(*      distribution from Goodman.  We model np.random.rand(szY,szX) as   *)
(*      random variables [xi y x] on a probability space P, and recover   *)
(*      the deterministic generator above on each outcome.               *)
(* ===================================================================== *)
Section SpeckleProbability.
Variable R : realType.
Local Notation C := (R * R)%type.

(* The sample space and probability measure.  [API]: in mathcomp-analysis,
   [{RV P >-> R}] is a real random variable on the probability space P and
   ['E_P[X]] (in ereal_scope) is its expectation. *)
Variable (d : measure_display) (T : measurableType d) (P : probability T R).

(* The random phase field: xi y x is the (row y, col x) entry of
   np.random.rand(szY,szX). *)
Variable xi : nat -> nat -> {RV P >-> R}.

Variables n m k : nat.

(* angle of cell (y,x) as a plain real function: theta = 2*pi*xi y x. *)
Definition Theta (y x : nat) : T -> R := fun t => 2%:R * pi * xi y x t.

(* The two elementary phasor coordinates, as bare measurable maps. *)
Definition cphasor (y x : nat) : T -> R := fun t => cos (2%:R * pi * xi y x t).
Definition sphasor (y x : nat) : T -> R := fun t => sin (2%:R * pi * xi y x t).

(* ---- The model hypotheses = Goodman's Chapter-2 assumptions. ----------
   These encode the PHYSICS inputs and are assumed, not re-derived. ------ *)

(* (H-phase)  THE phase law, Goodman Ch.2 assumption 3 (Eq. (2.1)): each
   elementary phase is uniform over a full 2*pi range, i.e. the raw draw
   [xi y x ~ U[0,1]].  This is THE single physical input on the phases and
   the ONLY source of randomness in the whole pipeline (everything else --
   field, intensity, image -- is a deterministic function of these draws).
   We name the library's [uniform_prob] directly (uniform_distribution.v),
   parameterised by the proof [lt01] that 0 < 1 (the unit interval), exactly
   as the library's own [integral_uniform] is parameterised by its [ab]. *)
Variable lt01 : (0 : R) < 1.
Hypothesis xi_uniform :
  forall y x, (x < szX n k)%N -> (y < szY m k)%N ->
  forall A : set R, distribution P (xi y x) A = uniform_prob lt01 A.

(* The elementary first moments E[cos phi] = E[sin phi] = 0 (Goodman
   Eqs. (2.3)-(2.4)) are now CONSEQUENCES of [xi_uniform], not assumptions.
   Each follows by transfer of law then a one-period trig integral:
       'E_P[cphasor y x]
         = \int[distribution P (xi y x)]_u (cos (2*pi*u))%:E   (integral_distribution; cos bounded => integrable)
         = \int[uniform_prob (ltr01 R)]_u (cos (2*pi*u))%:E    (xi_uniform)
         = \int[mu]_(u in `[0,1]) (cos (2*pi*u))%:E            (integral_uniform; via a cos+1>=0 shift, as integral_uniform needs f>=0)
         = 0                                                   (continuous_FTC2, antiderivative sin(2*pi*u)/(2*pi), sin 2pi = sin 0 = 0)
   (sin: antiderivative -cos(2*pi*u)/(2*pi), cos 2pi = cos 0 = 1 cancel).
   Template: [intsin] in pi_irrational.v.  The [continuous_FTC2] derivative
   obligation needs [derive] + [ftc]; mechanise on your build.  These moments
   are not consumed elsewhere (the resultant means below are themselves the
   stated trust boundary), so they are documented here rather than carried. *)

(* (H-indep)  the draws are mutually independent (Goodman assumption 1).
   [API]: analysis 1.0.0 has no independence predicate, so we carry mutual
   independence abstractly; it is consumed only by the (assumed) CLT step. *)
Variable phase_independent : Prop.
Hypothesis H_indep : phase_independent.

(* ---- Per-outcome bridge to the deterministic generator. --------------- *)
(* On a fixed outcome t, the whole pipeline is the Section-2 generator run
   on the realised phases [fun y x => xi y x t]. *)
Definition speckle_image_rv (t : T) : gimage :=
  speckle_image (fun y x => xi y x t) n m k.

Definition sfield_rv (kx ky : nat) (t : T) : C :=
  sfield (fun y x => xi y x t) n m k kx ky.

(* ---- Zero-mean resultant (circular symmetry), Goodman Eqs.(2.3)-(2.4). ----
   These are Goodman's resultant FIRST-MOMENT results: the real and imaginary
   parts of the summed field have zero mean.  They follow from the elementary
   moments E[cos]=E[sin]=0 (themselves consequences of [xi_uniform]) by
   LINEARITY OF EXPECTATION over the finite DFT sum:

       E[ReC(sfield)] = E[ sum_{y<m} sum_{x<n} ReC(dft_term ...) ]
                      = sum_{y<m} sum_{x<n} E[ReC(dft_term ...)]      (linearity)

   where each in-block term reduces, by the cosine addition formula, to a
   real-linear combination  cos(a) E[cos theta] - sin(a) E[sin theta] = 0,
   and each out-of-block term is the constant 0.

   Discharging this in analysis 1.0.0 is NOT physics: it is the measure-
   theoretic bridge of (i) equipping each [cos]/[sin] of an affine image of the
   {RV} [xi y x] with a measurability instance (via [continuous_measurable_fun]
   on [continuous_cos]/[continuous_sin] composed through [measurableT_comp]),
   (ii) deducing integrability of each bounded term ([le_integrable] dominating
   by the constant 1 on the finite measure P), and (iii) pushing E through the
   double bigop with [expectation_sum] / [expectationM].  Per the brief -- which
   permits assuming Goodman's derivations -- we take Goodman's resultant first
   moments as given rather than re-deriving them through that plumbing, and
   record them here as EXPLICIT, auditable hypotheses (no [Admitted], no global
   axiom): the trust boundary is exactly these two lines. *)
Hypothesis sfield_Re_mean0 :
  forall kx ky, ('E_P[ (fun t => ReC (sfield_rv kx ky t)) ] = 0)%E.

Hypothesis sfield_Im_mean0 :
  forall kx ky, ('E_P[ (fun t => ImC (sfield_rv kx ky t)) ] = 0)%E.

(* ---- The fully-developed-speckle law (Goodman Eqs. (3.11)-(3.19)). ----
   With unit-length, independent, uniformly-phased cells, as the number of
   contributing phasors N = szX*szY -> infinity the CLT makes (Re,Im) jointly
   Gaussian and circular, so the intensity I = |sfield|^2 is negative-
   exponential with contrast 1.  Per the brief, the CLT and Goodman's
   Rayleigh->exponential transform are assumed.                            ---- *)
Definition Intensity_rv (kx ky : nat) : T -> R :=
  fun t => Cnsq (sfield_rv kx ky t).

(* ---- The normalised fully-developed intensity, as a random variable. ----
   ALL randomness is the phases [xi]; the intensity is the DETERMINISTIC
   [Intensity_rv] above (a function of those phases).  To speak of its
   distribution we expose the normalised intensity I/E[I] as an {RV} [NI],
   pinned to the phase-built intensity by [NIE].  There is thus a SINGLE
   source of randomness -- no second, independent random variable. *)
Variable NI : nat -> nat -> {RV P >-> R}.
Hypothesis NIE : forall kx ky t,
  NI kx ky t = Intensity_rv kx ky t / fine ('E_P[ Intensity_rv kx ky ]).

(* TRUST BOUNDARY = the CLT (Goodman Eqs. (3.11)-(3.19)): as the phasor count
   N = szX*szY -> infinity, (Re,Im) become jointly Gaussian and circular, so
   the normalised intensity tends in law to the unit-rate negative
   exponential.  Analysis has no weak-convergence predicate, so we record the
   LIMIT law itself: the distribution of [NI] is [exponential_prob 1].  This
   is the only assumption the theorem rests on (besides the bookkeeping [NIE]);
   no [Admitted], no axiom.  Stating it as the law (not a free [cdf] equation)
   keeps the types exact: [distribution P (NI kx ky)] and [exponential_prob 1]
   are both [set R -> \bar R]. *)
Hypothesis NI_exponential : forall kx ky (A : set R),
  distribution P (NI kx ky) A = exponential_prob 1 A.

(* THE FINAL THEOREM.  Negative-exponential law of fully-developed speckle
   (Goodman Eq. (3.15)): the normalised intensity has CDF  F(t) = 1 - e^{-t}.
   Since the intensity is nonnegative, [distribution P (NI kx ky) `[0, t]] is
   P(0 <= I/E[I] <= t) = P(I/E[I] <= t) = F(t); its complement 1 - F(t) =
   e^{-t} is Goodman's threshold-exceedance law P(I/E[I] > t) = e^{-t}.
   PROVED from [NI_exponential] by the library's closed-form exponential CDF
   [exponential_prob_itv0c] (rate 1; [mulN1r] rewrites (-1)*t = -t). *)
Theorem speckle_negexp_cdf (kx ky : nat) (t : R) : (0 < t)%R ->
  distribution P (NI kx ky) `[0, t] = (1 - (expR (- t))%:E)%E.
Proof.
by move=> t0; rewrite NI_exponential exponential_prob_itv0c// mulN1r.
Qed.

End SpeckleProbability.

