(* ===================================================================== *)
(*  Speckle.v                                                            *)
(*                                                                       *)
(*  Faithful real/complex model of the generator from the email:         *)
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
(*  MODELLING CHOICES (so proofs stay accurate):                        *)
(*  - Randomness is an explicit input.  np.random.rand(szY,szX) is a     *)
(*    fresh draw of i.i.d. Uniform[0,1) values; we represent it by an    *)
(*    abstract [phase : nat -> nat -> R], read as phase ROW COL (i.e.    *)
(*    phase y x), with the intended interpretation phase y x in [0,1).   *)
(*    No distributional assumption is imposed here; to reason about the  *)
(*    PHYSICS (speckle contrast, the negative-exponential intensity      *)
(*    law, autocorrelation set by the spectral support) one layers a     *)
(*    probability measure on [phase] -- the natural place for a later    *)
(*    Coquelicot/MathComp-analysis development.                          *)
(*  - Index convention: x is the COLUMN (0..n-1), y is the ROW (0..m-1). *)
(*    fspace_full has numpy shape (m, n) = (rows, cols).                 *)
(*  - DFT sign: numpy's forward fft2 uses exp(-2*pi*i*...); we match it. *)
(*    (For the |.|^2 intensity the sign is immaterial, but we are        *)
(*    faithful anyway.)                                                  *)
(*  - astype(uint8) on values already scaled into [0,255] truncates      *)
(*    toward zero, i.e. floor for nonnegative reals; modelled by         *)
(*    Int_part.                                                          *)
(* ===================================================================== *)

From Coq Require Import Reals ZArith List Lia Bool.
Import ListNotations.
From SpecklePUF Require Import Complexes Image.

Local Open Scope R_scope.

Section Generator.
  (* The random phase field (np.random.rand(szY,szX)), read phase row col. *)
  Variable phase : nat -> nat -> R.
  (* n = real-space size x (width), m = size y (height), k = corr length. *)
  Variables n m k : nat.

  Definition szX : nat := Nat.div n k.   (* int(n/k) *)
  Definition szY : nat := Nat.div m k.   (* int(m/k) *)

  (* fspace_full[y][x]: exp(i 2π rand[y][x]) on the top-left szY x szX
     block, 0 elsewhere.  Indexed (x = col, y = row). *)
  Definition fspace (x y : nat) : C :=
    if (Nat.ltb x szX) && (Nat.ltb y szY)
    then Cexp (2 * PI * phase y x)
    else C0.

  (* 2-D forward DFT (numpy fft2), output at (kx = col, ky = row):
       F[ky,kx] = Σ_{y<m} Σ_{x<n} A[y,x] exp(-2πi (ky*y/m + kx*x/n)). *)
  Definition dft_term (kx ky x y : nat) : C :=
    Cmul (fspace x y)
         (Cexp (- (2 * PI) *
                 (INR ky * INR y / INR m + INR kx * INR x / INR n))).

  Definition sfield (kx ky : nat) : C :=
    Csum (map (fun y =>
                 Csum (map (fun x => dft_term kx ky x y) (seq 0 n)))
              (seq 0 m)).

  (* speckle_pattern: the intensity field |specklefield|^2 at (x=col,y=row). *)
  Definition speckle_pattern (x y : nat) : R := Cmod2 (sfield x y).

  (* Row-major coordinate list of the n x m grid. *)
  Definition coordsRM : list (nat * nat) :=
    flat_map (fun y => map (fun x => (x, y)) (seq 0 n)) (seq 0 m).

  (* speckle.max(): the maximum intensity over the grid. *)
  Definition maxI : R :=
    fold_left (fun acc p => Rmax acc (speckle_pattern (fst p) (snd p)))
              coordsRM 0.

  (* grayscale value = floor(255 * I / max) (astype uint8 on [0,255]). *)
  Definition gray (x y : nat) : nat :=
    if Rle_dec maxI 0 then 0%nat
    else Z.to_nat (Int_part (255 * speckle_pattern x y / maxI)).

  (* speckle_image: the resulting grayscale image (width n, height m). *)
  Definition speckle_image : gimage :=
    mkGImage n m
      (fun X Y =>
         if (0 <=? X)%Z && (X <? Z.of_nat n)%Z
            && (0 <=? Y)%Z && (Y <? Z.of_nat m)%Z
         then gray (Z.to_nat X) (Z.to_nat Y)
         else 0%nat).

End Generator.

(* The generated image has the requested dimensions. *)
Lemma speckle_image_dims :
  forall phase n m k,
    gw (speckle_image phase n m k) = n /\
    gh (speckle_image phase n m k) = m.
Proof. intros; split; reflexivity. Qed.

(* The intensity field is pointwise nonnegative (it is a squared modulus),
   which is what justifies the floor-normalization producing valid pixels. *)
Lemma speckle_pattern_nonneg :
  forall phase n m k x y, (0 <= speckle_pattern phase n m k x y)%R.
Proof. intros. apply Cmod2_nonneg. Qed.
