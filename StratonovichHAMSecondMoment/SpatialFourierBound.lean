module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`L:spatial-fourier-bound` (Deterministic Fourier bound for the spatial
energy) of `notes/integrated_spatial_occupation.tex` (revision a284420;
statement lines 101-111, display `E:spatial-fourier-bound` at lines 106-109,
proof lines 113-164), for the quantities `A_sp(g) = B_Γ(g², g²)` and
`b(g) = ‖∇g‖₂²` of lines 35-38 (with `B_Γ` of `E:spatial-physical-pair`,
lines 12-17).  This module proves `b(g) > 0` and the bound

  `0 ≤ A_sp(g) ≤ 2^{1+α} R_Γ(1) b(g)^{α/2}`  for every real unit `g ∈ C_c^∞(ℝ^d)`,

with `R_Γ(1) = ∫ μ(dξ)/(1+|ξ|²)` (`SpectralHomog.resolvent μ 1`; main TeX
lines 7714-7723 at a284420), under `H:homog` for every covariance it allows,
including `Γ = 0` and singular ones, as in the lemma
(`spatial_fourier_bound_paper`).  The lemma writes the constant as `R_α` of
`E:intro-spectral-mass` (main TeX line 531) and uses `R_Γ(q) = q^{α-2} R_α`
(this file, lines 149-155); the identity `R_Γ(1) = R_α` is not formalized here, so the
Lean constant is `R_Γ(1)`.

The manuscript uses this lemma for the first claim of `P:spatial-smooth-ratio`
(lines 166-170, proof lines 185-188): `R_0 = sup A_sp(g)/b(g)^{α/2}` is finite
without the finiteness of `S_1^pos`, hence without `T:full-upper`.  The
consequence for `R_0` itself is drawn in `SpatialSmoothRatio`.

Proof route (the TeX proof, lines 113-164, takes the same steps; lemmas with
no sentence in it are marked "Auxiliary to the Lean proof route"):
* `A_sp(g) = ∫ c_Q dΓ` with `Q = g²` and the autocorrelation
  `c_Q(y) = ∫ Q(x) Q(x-y) dx`; `c_Q = Q ⋆ Q(-·)` is smooth with compact support,
  hence a Schwartz function (`HasCompactSupport.toSchwartzMap`), so the spectral
  convention `HomogHypothesis.IsSpectralMeasure` applies to it;
* `∫ c_Q(x) e^{iξ·x} dx = |Q̂(ξ)|²` (hand Fubini on `ℝ^d × ℝ^d`,
  `fourier_autocorr`), so `A_sp(g) = ∫ |Q̂|² dμ` (`integral_autocorr_eq_spectral`);
* `|Q̂| ≤ ‖Q‖₁ = 1` and, by integration by parts with `𝕜 = ℂ`
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`),
  `|ξ| |Q̂(ξ)| ≤ ‖∂_ξ(g²)‖₁/|ξ| ≤ 2√b` (with `2|g||∇g| ≤ √b g² + |∇g|²/√b`);
  hence `|Q̂|² (4b + |ξ|²) ≤ 8b`, i.e. `|Q̂|² ≤ 8b/(4b+|ξ|²)`;
* `∫ μ(dξ)/(4b+|ξ|²) = R_Γ(2√b) = (2√b)^{α-2} R_Γ(1)` by
  `SpectralHomog.resolvent_homog`, with `μ` homogeneous by
  `MaskedSpectralGrowth.spectralHomogeneous_of_homog`, and the integrability of
  `(1+|ξ|²)^{-1}` from `SpectralHomog.integrable_inv_one_add_sq` (`α < 2`).

Also proved: `b(g) > 0` for a real unit `g ∈ C_c^∞(ℝ^d)` when `d ≥ 1`
(`gradEnergy_pos`; the statement of the lemma, line 105, proof lines
114-115; TeX lines 180-182 state it again for `P:spatial-smooth-ratio`).
`b = 0` forces `∇g ≡ 0`, so `g` is constant and, having compact support in
the noncompact `ℝ^d`, zero, as in the proof of the lemma; the proof of
`P:spatial-smooth-ratio` argues instead through the Fourier support of a
function with zero weak gradient (same conclusion).

Definitions: `autocorr` (`c_Q`), `spatialPair` (`B_Γ(F,G)` as the iterated
Bochner integral `∫ (∫ F(x) G(x-y) dx) Γ(dy)`; for the continuous compactly
supported functions used here it is absolutely convergent; the `[0,∞]`-valued
form `OccupationKernelRow.pairing` is not used, and the identification of the
two is not proved here; for continuous, compactly supported, nonnegative
functions and locally finite `Γ` it is `SpatialStaticControls.pairing_eq_spatialPair`),
`spatialEnergy` (`A_sp`),
`gradEnergy` (`b`, through the operator norm of `fderiv`, which equals the
Euclidean norm of the gradient), `fourierQ` (`Q̂(ξ) = ∫ Q(x) e^{iξ·x} dx`, the
convention of `IsSpectralMeasure`; the TeX proof's `F_0 Q` of lines 116-118
has the exponent `e^{-iξ·x}`, so `Q̂ = conj(F_0 Q)` for real `Q`, with the
same modulus), `IsUnitTest` (smooth, compact support, `∫ g² = 1`).

Supplied inputs: none.  Implicit hypotheses made explicit: the integrability of
`c_Q` against `Γ`, of `|Q̂|²` and of `(1+|ξ|²)^{-1}` against `μ` are part of
the conclusions (a Lean Bochner integral of a non-integrable function is `0`).
Hypotheses of `H:homog` used by the wrapper: `dim` (for `d ≥ 1`),
`alpha0_pos` and `threshold` (for `α < 2`), `Γ_radon`, `μ_radon`, `spectral`,
`μ_tempered` and `scaling` (the last two through
`spectralHomogeneous_of_homog`); the other fields are carried, unused.  No
`Γ ≠ 0` is assumed (the bound holds for `Γ = 0`).  Lemmas marked "Auxiliary to
the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Metric
open scoped ContDiff Convolution ENNReal ComplexConjugate

namespace StratonovichHAMSecondMoment.SpatialFourierBound

open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure)

variable {d : ℕ}

/-! ### Definitions -/

/-- A step of the proof of `L:spatial-fourier-bound` (TeX lines 122-125): the autocorrelation
`c_Q(y) = ∫ Q(x) Q(x - y) dx` (the inner integral of `B_Γ(Q,Q)` in
`E:spatial-physical-pair`).  This is the package's one autocorrelation
(`VariationalFloor` F3 is stated for it). -/
def autocorr (Q : Rd d → ℝ) (y : Rd d) : ℝ := ∫ x, Q x * Q (x - y)

/-- The real form of the physical pairing `E:spatial-physical-pair`
(`integrated_spatial_occupation.tex` lines 15-17):
`B_Γ(F,G) = ∫ (∫ F(x) G(x - y) dx) Γ(dy)`, as an iterated Bochner integral.
For the continuous compactly supported functions used here it is an absolutely
convergent integral (see `integrable_autocorr` and `SpatialSmoothRatio`). -/
def spatialPair (Γ : Measure (Rd d)) (F G : Rd d → ℝ) : ℝ :=
  ∫ y, (∫ x, F x * G (x - y)) ∂Γ

/-- `A_sp(g) = B_Γ(g², g²)` (line 35). -/
def spatialEnergy (Γ : Measure (Rd d)) (g : Rd d → ℝ) : ℝ :=
  spatialPair Γ (fun x => g x ^ 2) (fun x => g x ^ 2)

/-- `b(g) = ‖∇g‖₂²` (line 35), for a differentiable `g`, through the operator
norm of the Fréchet derivative (equal to the Euclidean norm of the gradient). -/
def gradEnergy (g : Rd d → ℝ) : ℝ := ∫ x, ‖fderiv ℝ g x‖ ^ 2

/-- A step of the proof of `L:spatial-fourier-bound` (TeX lines 116-118, up to complex conjugation): the Fourier transform in the manuscript's
convention (the one of `HomogHypothesis.IsSpectralMeasure`):
`Q̂(ξ) = ∫ Q(x) e^{i ξ·x} dx`. -/
def fourierQ (Q : Rd d → ℝ) (ξ : Rd d) : ℂ :=
  ∫ x, (Q x : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))

/-- A real unit profile `g ∈ C_c^∞(ℝ^d)`: smooth, compactly supported, `‖g‖₂ = 1`. -/
def IsUnitTest (g : Rd d → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∫ x, g x ^ 2 = 1

/-! ### The autocorrelation as a Schwartz function -/

/-- Auxiliary to the Lean proof route: the autocorrelation is the convolution
`Q ⋆ Q(-·)`. -/
theorem autocorr_eq_convolution (Q : Rd d → ℝ) :
    autocorr Q = convolution Q (fun x => Q (-x)) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext y
  simp only [autocorr, convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul, neg_sub]

/-- A step of the proof of `L:spatial-fourier-bound` (TeX line 126). -/
theorem autocorr_contDiff {Q : Rd d → ℝ} (hQ : ContDiff ℝ ∞ Q) (hc : HasCompactSupport Q) :
    ContDiff ℝ ∞ (autocorr Q) := by
  rw [autocorr_eq_convolution]
  have hl : LocallyIntegrable (fun x => Q (-x)) volume :=
    (hQ.continuous.comp continuous_neg).locallyIntegrable
  exact hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hQ hl

/-- A step of the proof of `L:spatial-fourier-bound` (TeX line 126). -/
theorem autocorr_hasCompactSupport {Q : Rd d → ℝ} (hc : HasCompactSupport Q) :
    HasCompactSupport (autocorr Q) := by
  rw [autocorr_eq_convolution]
  exact hc.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hc.comp_homeomorph (Homeomorph.neg _))

/-- Auxiliary to the Lean proof route. -/
theorem autocorr_continuous {Q : Rd d → ℝ} (hQ : Continuous Q) (hc : HasCompactSupport Q) :
    Continuous (autocorr Q) := by
  rw [autocorr_eq_convolution]
  exact (hc.comp_homeomorph (Homeomorph.neg _)).continuous_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hQ.locallyIntegrable (hQ.comp continuous_neg)

/-- Auxiliary to the Lean proof route: the autocorrelation of a nonnegative function is nonnegative. -/
theorem autocorr_nonneg {Q : Rd d → ℝ} (h0 : ∀ x, 0 ≤ Q x) (y : Rd d) : 0 ≤ autocorr Q y :=
  integral_nonneg fun x => mul_nonneg (h0 x) (h0 (x - y))

/-- A step of the proof of `L:spatial-fourier-bound` (TeX lines 134-135): integrability of a continuous compactly
supported function against a locally finite measure. -/
theorem integrable_autocorr {Q : Rd d → ℝ} (hQ : Continuous Q) (hc : HasCompactSupport Q)
    (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] : Integrable (autocorr Q) Γ :=
  (autocorr_continuous hQ hc).integrable_of_hasCompactSupport (autocorr_hasCompactSupport hc)

/-! ### The Fourier transform of the autocorrelation -/

/-- Auxiliary to the Lean proof route: the exponential `e_ξ(x) = e^{i ξ·x}`. -/
abbrev ex (ξ x : Rd d) : ℂ := Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))

/-- Auxiliary to the Lean proof route. -/
theorem ex_continuous (ξ : Rd d) : Continuous (ex ξ) := by
  unfold ex; fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem norm_ex (ξ x : Rd d) : ‖ex ξ x‖ = 1 := by
  rw [ex, Complex.norm_exp]
  simp

/-- Auxiliary to the Lean proof route: `e_ξ(z - w) = e_ξ(z) conj(e_ξ(w))`. -/
theorem ex_sub (ξ z w : Rd d) : ex ξ (z - w) = ex ξ z * conj (ex ξ w) := by
  simp only [ex, inner_sub_right, ← Complex.exp_conj, ← Complex.exp_add, map_mul,
    Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

/-- Auxiliary to the Lean proof route: a compact set containing the support of
`(x, z) ↦ Q(z) Q(z - x)`. -/
theorem prod_hasCompactSupport {Q : Rd d → ℝ} (hc : HasCompactSupport Q) (ξ : Rd d) :
    HasCompactSupport (Function.uncurry fun (x z : Rd d) =>
      ((Q z * Q (z - x) : ℝ) : ℂ) * ex ξ x) := by
  have hK : IsCompact (tsupport Q) := HasCompactSupport.isCompact hc
  refine HasCompactSupport.intro
    (((hK.prod hK).image (continuous_fst.sub continuous_snd)).prod hK) ?_
  rintro ⟨x, z⟩ hxz
  simp only [Function.uncurry_apply_pair]
  by_cases hz : z ∈ tsupport Q
  · by_cases hzx : z - x ∈ tsupport Q
    · exfalso
      apply hxz
      exact ⟨⟨(z, z - x), ⟨hz, hzx⟩, by simp⟩, hz⟩
    · rw [image_eq_zero_of_notMem_tsupport hzx]; simp
  · rw [image_eq_zero_of_notMem_tsupport hz]; simp

/-- A step of the proof of `L:spatial-fourier-bound` (TeX line 128): the Fourier transform of the autocorrelation is `|Q̂|²`:
`∫ c_Q(x) e^{i ξ·x} dx = |Q̂(ξ)|²` for continuous compactly supported real `Q`
(hand Fubini on `ℝ^d × ℝ^d` and the substitution `x ↦ z - x`). -/
theorem fourier_autocorr {Q : Rd d → ℝ} (hQ : Continuous Q) (hc : HasCompactSupport Q)
    (ξ : Rd d) :
    ∫ x, (autocorr Q x : ℂ) * ex ξ x = ((‖fourierQ Q ξ‖ ^ 2 : ℝ) : ℂ) := by
  have hint : Integrable (Function.uncurry fun (x z : Rd d) =>
      ((Q z * Q (z - x) : ℝ) : ℂ) * ex ξ x) (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (prod_hasCompactSupport hc ξ)
    refine Continuous.mul ?_ ((ex_continuous ξ).comp continuous_fst)
    exact Complex.continuous_ofReal.comp ((hQ.comp continuous_snd).mul
      (hQ.comp (continuous_snd.sub continuous_fst)))
  have step1 : ∀ x, (autocorr Q x : ℂ) * ex ξ x =
      ∫ z, ((Q z * Q (z - x) : ℝ) : ℂ) * ex ξ x := by
    intro x
    rw [autocorr, integral_mul_const, integral_complex_ofReal]
  simp_rw [step1]
  rw [integral_integral_swap hint]
  have inner : ∀ z, ∫ x, ((Q z * Q (z - x) : ℝ) : ℂ) * ex ξ x =
      (Q z : ℂ) * ex ξ z * conj (fourierQ Q ξ) := by
    intro z
    have h1 : ∀ x, ((Q z * Q (z - x) : ℝ) : ℂ) * ex ξ x =
        (Q z : ℂ) * ((fun w => (Q w : ℂ) * ex ξ (z - w)) (z - x)) := by
      intro x
      simp only [sub_sub_cancel]
      push_cast; ring
    simp_rw [h1]
    rw [integral_const_mul, integral_sub_left_eq_self (fun w => (Q w : ℂ) * ex ξ (z - w))]
    simp_rw [ex_sub]
    have h2 : ∀ w, (Q w : ℂ) * (ex ξ z * conj (ex ξ w)) =
        ex ξ z * conj ((Q w : ℂ) * ex ξ w) := by
      intro w; rw [map_mul, Complex.conj_ofReal]; ring
    simp_rw [h2]
    rw [integral_const_mul, integral_conj]
    rw [fourierQ]
    ring
  simp_rw [inner]
  rw [integral_mul_const]
  have h3 : ∫ z, (Q z : ℂ) * ex ξ z = fourierQ Q ξ := rfl
  rw [h3, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A step of the proof of `L:spatial-fourier-bound` (TeX lines 126-133): the spectral form of `A`: for smooth compactly supported real `Q` and a
spectral measure `μ` of `Γ` (`IsSpectralMeasure`, the manuscript's convention),
`∫ c_Q dΓ = ∫ |Q̂|² dμ` as Bochner integrals.  (No integrability is asserted
here; see `spatial_fourier_bound` for the integrability of both sides.) -/
theorem integral_autocorr_eq_spectral {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ)
    {Q : Rd d → ℝ} (hQ : ContDiff ℝ ∞ Q) (hc : HasCompactSupport Q) :
    ∫ y, autocorr Q y ∂Γ = ∫ ξ, ‖fourierQ Q ξ‖ ^ 2 ∂μ := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (autocorr Q x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (autocorr_contDiff hQ hc)
  have hcs : HasCompactSupport (fun x => (autocorr Q x : ℂ)) :=
    (autocorr_hasCompactSupport hc).comp_left Complex.ofReal_zero
  have h := hsp (hcs.toSchwartzMap hsm)
  simp only [HasCompactSupport.toSchwartzMap_toFun] at h
  have h2 : ∀ ξ, ∫ x, (autocorr Q x : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
      ((‖fourierQ Q ξ‖ ^ 2 : ℝ) : ℂ) := fun ξ => fourier_autocorr hQ.continuous hc ξ
  simp_rw [h2, integral_complex_ofReal] at h
  exact_mod_cast h

/-! ### Pointwise bounds on `Q̂` -/

/-- A step of the proof of `L:spatial-fourier-bound` (TeX line 138): `|Q̂(ξ)| ≤ ‖Q‖₁`. -/
theorem norm_fourierQ_le (Q : Rd d → ℝ) (ξ : Rd d) :
    ‖fourierQ Q ξ‖ ≤ ∫ x, |Q x| := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x
  rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Auxiliary to the Lean proof route: the derivative of `e_ξ`,
`∂_v e_ξ(x) = e_ξ(x) · i ξ·v`. -/
theorem fderiv_ex (ξ x v : Rd d) :
    fderiv ℝ (ex ξ) x v = ex ξ x * (Complex.I * (inner ℝ ξ v : ℝ)) := by
  have hL : HasFDerivAt (fun y : Rd d => ((inner ℝ ξ y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (innerSL ℝ ξ)) x :=
    (Complex.ofRealCLM.comp (innerSL ℝ ξ)).hasFDerivAt
  have h := (hL.const_mul Complex.I).cexp
  rw [h.fderiv]
  simp [ex]

/-- Auxiliary to the Lean proof route: the derivative of the complexified
real function. -/
theorem fderiv_ofReal {Q : Rd d → ℝ} {x : Rd d} (hQ : DifferentiableAt ℝ Q x) (v : Rd d) :
    fderiv ℝ (fun y => (Q y : ℂ)) x v = (fderiv ℝ Q x v : ℂ) := by
  have h : HasFDerivAt (fun y => (Q y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Q x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hQ.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- A step of the proof of `L:spatial-fourier-bound` (TeX lines 138-142): integration by parts (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`
with `𝕜 = ℂ`): for `Q ∈ C_c^1(ℝ^d; ℝ)`, `|ξ·v| |Q̂(ξ)| ≤ ∫ |∂_v Q|`. -/
theorem inner_mul_norm_fourierQ_le {Q : Rd d → ℝ} (hQ : ContDiff ℝ 1 Q)
    (hc : HasCompactSupport Q) (ξ v : Rd d) :
    |inner ℝ ξ v| * ‖fourierQ Q ξ‖ ≤ ∫ x, |fderiv ℝ Q x v| := by
  have hdiff : Differentiable ℝ Q := hQ.differentiable one_ne_zero
  have hDc : Continuous (fun x => fderiv ℝ Q x v) :=
    (hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDcs : HasCompactSupport (fun x => fderiv ℝ Q x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : Rd d →L[ℝ] ℝ => L v) rfl
  have hQc : HasCompactSupport (fun x => (Q x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have e1 : (fun x => fderiv ℝ (fun y => (Q y : ℂ)) x v * ex ξ x) =
      fun x => (fderiv ℝ Q x v : ℂ) * ex ξ x := by
    funext x; rw [fderiv_ofReal (hdiff x)]
  have e2 : (fun x => (Q x : ℂ) * fderiv ℝ (ex ξ) x v) =
      fun x => (Complex.I * (inner ℝ ξ v : ℝ)) * ((Q x : ℂ) * ex ξ x) := by
    funext x; rw [fderiv_ex]; ring
  have i1 : Integrable (fun x => fderiv ℝ (fun y => (Q y : ℂ)) x v * ex ξ x) volume := by
    rw [e1]
    exact ((Complex.continuous_ofReal.comp hDc).mul (ex_continuous ξ)).integrable_of_hasCompactSupport
      ((hDcs.comp_left Complex.ofReal_zero).mul_right)
  have i3 : Integrable (fun x => (Q x : ℂ) * ex ξ x) volume :=
    ((Complex.continuous_ofReal.comp hQ.continuous).mul (ex_continuous ξ)).integrable_of_hasCompactSupport
      hQc.mul_right
  have i2 : Integrable (fun x => (Q x : ℂ) * fderiv ℝ (ex ξ) x v) volume := by
    rw [e2]; exact i3.const_mul _
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y => (Q y : ℂ)) (g := ex ξ) (v := v) i1 i2 i3
    (fun x _ => (Complex.ofRealCLM.differentiable.comp hdiff) x)
    (fun x _ => (Complex.differentiable_exp.comp ((differentiable_const _).mul
      (Complex.ofRealCLM.differentiable.comp (innerSL ℝ ξ).differentiable))) x)
  rw [e2, e1, integral_const_mul] at key
  have hn : ‖(Complex.I * (inner ℝ ξ v : ℝ)) * fourierQ Q ξ‖ = |inner ℝ ξ v| * ‖fourierQ Q ξ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [← hn]
  have : (Complex.I * (inner ℝ ξ v : ℝ)) * fourierQ Q ξ =
      -∫ x, (fderiv ℝ Q x v : ℂ) * ex ξ x := key
  rw [this, norm_neg]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x
  rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Auxiliary to the Lean proof route: `∂_v (g²) = 2 g ∂_v g`. -/
theorem fderiv_sq_apply {g : Rd d → ℝ} {x : Rd d} (hg : DifferentiableAt ℝ g x) (v : Rd d) :
    fderiv ℝ (fun y => g y ^ 2) x v = 2 * g x * fderiv ℝ g x v := by
  rw [(hg.hasFDerivAt.pow 2).fderiv]
  simp

/-- Auxiliary to the Lean proof route: integrability of `g²` and `‖∇g‖²` for a
smooth compactly supported `g`. -/
theorem integrable_sq_and_grad {g : Rd d → ℝ} (hs : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    Integrable (fun x => g x ^ 2) volume ∧ Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) volume := by
  have hD : Continuous (fderiv ℝ g) := hs.continuous_fderiv (by simp)
  have hc1 : HasCompactSupport (fun x => g x ^ 2) :=
    hc.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have hc2 : HasCompactSupport (fun x => ‖fderiv ℝ g x‖ ^ 2) :=
    (hc.fderiv ℝ).comp_left (g := fun L : Rd d →L[ℝ] ℝ => ‖L‖ ^ 2) (by simp)
  have hk1 : Continuous (fun x => g x ^ 2) := hs.continuous.pow 2
  have hk2 : Continuous (fun x => ‖fderiv ℝ g x‖ ^ 2) := hD.norm.pow 2
  exact ⟨hk1.integrable_of_hasCompactSupport hc1, hk2.integrable_of_hasCompactSupport hc2⟩

/-- Auxiliary to the Lean proof route: the gradient energy is nonnegative. -/
theorem gradEnergy_nonneg (g : Rd d → ℝ) : 0 ≤ gradEnergy g :=
  integral_nonneg fun _ => by positivity

/-- A step of the proof of `L:spatial-fourier-bound` (TeX lines 138-144): `|ξ| |Q̂(ξ)| ≤ 2 √b` for `Q = g²`, `g` a unit test with `b = ‖∇g‖₂² > 0`
(the derivative bound `|ξ·v||Q̂| ≤ ‖∂_v Q‖₁` with `v = ξ`, `∂_ξ(g²) = 2g∂_ξ g`,
and `2|g||∇g| ≤ √b g² + |∇g|²/√b`). -/
theorem norm_mul_norm_fourierQ_le {g : Rd d → ℝ} (hg : IsUnitTest g) (hb : 0 < gradEnergy g)
    (ξ : Rd d) :
    ‖ξ‖ * ‖fourierQ (fun x => g x ^ 2) ξ‖ ≤ 2 * Real.sqrt (gradEnergy g) := by
  obtain ⟨hs, hc, hu⟩ := hg
  obtain ⟨i1, i2⟩ := integrable_sq_and_grad hs hc
  have hdiff : Differentiable ℝ g := hs.differentiable (by simp)
  set b := gradEnergy g with hbdef
  set t := Real.sqrt b with htdef
  have ht : 0 < t := Real.sqrt_pos.2 hb
  have htt : t * t = b := Real.mul_self_sqrt hb.le
  have hQ1 : ContDiff ℝ 1 (fun x => g x ^ 2) := (hs.pow 2).of_le (by simp)
  have hQc : HasCompactSupport (fun x => g x ^ 2) :=
    hc.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have h1 := inner_mul_norm_fourierQ_le hQ1 hQc ξ ξ
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (by positivity)] at h1
  have hpt : ∀ x, |fderiv ℝ (fun y => g y ^ 2) x ξ| ≤
      ‖ξ‖ * (t * g x ^ 2 + ‖fderiv ℝ g x‖ ^ 2 / t) := by
    intro x
    rw [fderiv_sq_apply (hdiff x)]
    have hle : |fderiv ℝ g x ξ| ≤ ‖fderiv ℝ g x‖ * ‖ξ‖ := by
      rw [← Real.norm_eq_abs]; exact (fderiv ℝ g x).le_opNorm ξ
    have amgm : 2 * |g x| * ‖fderiv ℝ g x‖ ≤ t * g x ^ 2 + ‖fderiv ℝ g x‖ ^ 2 / t := by
      rw [← sq_abs (g x)]
      have : 0 ≤ (t * |g x| - ‖fderiv ℝ g x‖) ^ 2 := sq_nonneg _
      rw [div_eq_mul_inv]
      have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
      nlinarith [inv_pos.2 ht, mul_nonneg (inv_pos.2 ht).le this]
    calc |2 * g x * fderiv ℝ g x ξ| = 2 * |g x| * |fderiv ℝ g x ξ| := by
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ 2 * |g x| * (‖fderiv ℝ g x‖ * ‖ξ‖) := by gcongr
      _ = ‖ξ‖ * (2 * |g x| * ‖fderiv ℝ g x‖) := by ring
      _ ≤ ‖ξ‖ * (t * g x ^ 2 + ‖fderiv ℝ g x‖ ^ 2 / t) := by gcongr
  have hint_r : Integrable (fun x => ‖ξ‖ * (t * g x ^ 2 + ‖fderiv ℝ g x‖ ^ 2 / t)) volume :=
    ((i1.const_mul t).add (i2.div_const t)).const_mul _
  have hDQc : Continuous (fun x => fderiv ℝ (fun y => g y ^ 2) x ξ) :=
    (hQ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint_l : Integrable (fun x => |fderiv ℝ (fun y => g y ^ 2) x ξ|) volume :=
    hDQc.abs.integrable_of_hasCompactSupport
      (((hQc.fderiv ℝ).comp_left (g := fun L : Rd d →L[ℝ] ℝ => L ξ) rfl).comp_left
        (g := fun r : ℝ => |r|) (by simp))
  have h2 := integral_mono hint_l hint_r hpt
  rw [integral_const_mul, integral_add (i1.const_mul t) (i2.div_const t), integral_const_mul,
    integral_div, hu] at h2
  change _ ≤ ‖ξ‖ * (t * 1 + b / t) at h2
  have h3 : t * 1 + b / t = 2 * t := by
    rw [← htt]; field_simp; ring
  rw [h3] at h2
  have h4 : ‖ξ‖ * (‖ξ‖ * ‖fourierQ (fun x => g x ^ 2) ξ‖) ≤ ‖ξ‖ * (2 * t) := by
    calc _ = ‖ξ‖ ^ 2 * ‖fourierQ (fun x => g x ^ 2) ξ‖ := by ring
      _ ≤ _ := h1.trans h2
  rcases (norm_nonneg ξ).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; positivity
  · exact le_of_mul_le_mul_left h4 h0

/-- A step of the proof of `L:spatial-fourier-bound` (TeX lines 145-148): `|Q̂(ξ)|² (4b + |ξ|²) ≤ 8b` for `Q = g²`, `g` a unit test, `b > 0`; hence
`|Q̂|² ≤ min(1, 4b/|ξ|²)` up to the factor `2`. -/
theorem norm_fourierQ_sq_mul_le {g : Rd d → ℝ} (hg : IsUnitTest g) (hb : 0 < gradEnergy g)
    (ξ : Rd d) :
    ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2 * (4 * gradEnergy g + ‖ξ‖ ^ 2) ≤ 8 * gradEnergy g := by
  have h1 : ‖fourierQ (fun x => g x ^ 2) ξ‖ ≤ 1 := by
    refine (norm_fourierQ_le _ ξ).trans (le_of_eq ?_)
    simp_rw [abs_pow, sq_abs]
    exact hg.2.2
  have h2 := norm_mul_norm_fourierQ_le hg hb ξ
  set F := ‖fourierQ (fun x => g x ^ 2) ξ‖
  have hF : 0 ≤ F := norm_nonneg _
  have hs : Real.sqrt (gradEnergy g) ^ 2 = gradEnergy g := Real.sq_sqrt hb.le
  have h3 : (‖ξ‖ * F) ^ 2 ≤ 4 * gradEnergy g := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    have e : (2 * Real.sqrt (gradEnergy g)) ^ 2 = 4 * gradEnergy g := by
      rw [mul_pow, hs]; norm_num
    linarith
  have h4 : F ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ 4 * gradEnergy g)]

/-- Auxiliary to the Lean proof route: `Q̂` is continuous for integrable `Q`
(dominated convergence). -/
theorem fourierQ_continuous {Q : Rd d → ℝ} (hQ : Integrable Q volume) :
    Continuous (fourierQ Q) := by
  refine continuous_of_dominated (bound := fun x => |Q x|) (fun ξ => ?_) (fun ξ => ?_)
    hQ.abs (Eventually.of_forall fun x => ?_)
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hQ.aestronglyMeasurable).mul
      (ex_continuous ξ).aestronglyMeasurable
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · exact continuous_const.mul (by fun_prop)

/-- A step of the proof of `L:spatial-fourier-bound` (TeX lines 156-160): the scalar identity
`8 b (2√b)^{α-2} = 2^{1+α} b^{α/2}` for `b > 0`. -/
theorem scalar_identity (alpha b : ℝ) (hb : 0 < b) :
    8 * b * (2 * Real.sqrt b) ^ (alpha - 2) = 2 ^ (1 + alpha) * b ^ (alpha / 2) := by
  rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg b), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hb.le]
  have h8 : (8 : ℝ) = 2 ^ (3 : ℝ) := by norm_num
  have e1 : (2 : ℝ) ^ (1 + alpha) = 2 ^ (3 : ℝ) * 2 ^ (alpha - 2) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have e2 : b ^ (alpha / 2) = b * b ^ (1 / 2 * (alpha - 2)) := by
    have : b * b ^ (1 / 2 * (alpha - 2)) = b ^ (1 : ℝ) * b ^ (1 / 2 * (alpha - 2)) := by
      rw [Real.rpow_one]
    rw [this, ← Real.rpow_add hb]
    congr 1; ring
  rw [e1, e2, h8]
  ring

/-- **The deterministic Fourier bound** (general form of
`E:spatial-fourier-bound`, TeX lines 106-109; see the module doc).  Let `Γ, μ`
be locally
finite measures on `ℝ^d` with `μ` a spectral measure of `Γ` in the
manuscript's convention (`IsSpectralMeasure`), `μ` homogeneous of degree `α`
(`SpectralHomog.SpectralHomogeneous`) and `α < 2`.  For a real unit
`g ∈ C_c^∞(ℝ^d)` with `b = ‖∇g‖₂² > 0` and `Q = g²`:
the autocorrelation `c_Q` is `Γ`-integrable, `|Q̂|²` and `(1+|ξ|²)^{-1}` are
`μ`-integrable, `A_sp(g) = ∫ |Q̂|² dμ ≥ 0`, and
`A_sp(g) ≤ 2^{1+α} R_Γ(1) b^{α/2}` with `R_Γ(1) = ∫ μ(dξ)/(1+|ξ|²)`
(`SpectralHomog.resolvent μ 1`). -/
theorem spatial_fourier_bound {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    [IsLocallyFiniteMeasure μ] (hsp : IsSpectralMeasure Γ μ) {alpha : ℝ}
    (hI : SpectralHomog.SpectralHomogeneous μ alpha) (ha2 : alpha < 2)
    {g : Rd d → ℝ} (hg : IsUnitTest g) (hb : 0 < gradEnergy g) :
    Integrable (autocorr (fun x => g x ^ 2)) Γ ∧
      Integrable (fun ξ => ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2) μ ∧
      Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ ∧
      spatialEnergy Γ g = ∫ ξ, ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2 ∂μ ∧
      0 ≤ spatialEnergy Γ g ∧
      spatialEnergy Γ g ≤
        2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1 * gradEnergy g ^ (alpha / 2) := by
  obtain ⟨hs, hc, hu⟩ := hg
  have hQs : ContDiff ℝ ∞ (fun x => g x ^ 2) := hs.pow 2
  have hQc : HasCompactSupport (fun x => g x ^ 2) :=
    hc.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have i1 := integrable_autocorr hQs.continuous hQc Γ
  have hR := SpectralHomog.integrable_inv_one_add_sq hI ha2
  set b := gradEnergy g with hbdef
  set q := 2 * Real.sqrt b with hqdef
  have hq : 0 < q := by positivity
  have hq2 : q ^ 2 = 4 * b := by rw [hqdef, mul_pow, Real.sq_sqrt hb.le]; norm_num
  have hRq := SpectralHomog.resolvent_integrable hR q hq.ne'
  have hpt : ∀ ξ, ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2 ≤ 8 * b * (1 / (q ^ 2 + ‖ξ‖ ^ 2)) := by
    intro ξ
    have h := norm_fourierQ_sq_mul_le ⟨hs, hc, hu⟩ hb ξ
    rw [hq2, mul_one_div, le_div_iff₀ (by positivity)]
    exact h
  have hmeas : AEStronglyMeasurable (fun ξ => ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2) μ :=
    ((fourierQ_continuous (integrable_sq_and_grad hs hc).1).norm.pow 2).aestronglyMeasurable
  have i2 : Integrable (fun ξ => ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2) μ :=
    Integrable.mono' (hRq.const_mul (8 * b)) hmeas (Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hpt ξ)
  have heq : spatialEnergy Γ g = ∫ ξ, ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2 ∂μ :=
    integral_autocorr_eq_spectral hsp hQs hQc
  refine ⟨i1, i2, hR, heq, ?_, ?_⟩
  · rw [heq]; exact integral_nonneg fun _ => by positivity
  · rw [heq]
    calc ∫ ξ, ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2 ∂μ
        ≤ ∫ ξ, 8 * b * (1 / (q ^ 2 + ‖ξ‖ ^ 2)) ∂μ :=
          integral_mono i2 (hRq.const_mul _) hpt
      _ = 8 * b * SpectralHomog.resolvent μ q := by
          rw [integral_const_mul]; rfl
      _ = 8 * b * (q ^ (alpha - 2) * SpectralHomog.resolvent μ 1) := by
          rw [SpectralHomog.resolvent_homog hI q hq]
      _ = 2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1 * b ^ (alpha / 2) := by
          rw [← mul_assoc, scalar_identity alpha b hb]; ring

/-! ### Positivity of the gradient energy -/

/-- `b(g) > 0` for a real unit `g ∈ C_c^∞(ℝ^d)`, `d ≥ 1` (the `b > 0` of
`L:spatial-fourier-bound`, TeX line 105, proof lines 114-115; stated again in
the proof of `P:spatial-smooth-ratio`, lines 180-182, which argues by Fourier
support).  As in the proof of the lemma:
`b = 0` forces `∇g ≡ 0` by continuity, hence `g` constant, hence `g = 0` by
compact support in the noncompact `ℝ^d`, contradicting `‖g‖₂ = 1`.  For `d = 0`
the claim is false (`ℝ⁰` is a point), so `0 < d` is needed. -/
theorem gradEnergy_pos (hd : 0 < d) {g : Rd d → ℝ} (hg : IsUnitTest g) :
    0 < gradEnergy g := by
  obtain ⟨hs, hc, hu⟩ := hg
  obtain ⟨_, i2⟩ := integrable_sq_and_grad hs hc
  have hD : Continuous (fderiv ℝ g) := hs.continuous_fderiv (by simp)
  rcases (gradEnergy_nonneg g).eq_or_lt with h0 | h0
  · exfalso
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) i2).1 h0.symm
    have hall : (fun x => ‖fderiv ℝ g x‖ ^ 2) = fun _ => (0 : ℝ) :=
      (Continuous.ae_eq_iff_eq volume (hD.norm.pow 2) continuous_const).1 hae
    have hz : ∀ x, fderiv ℝ g x = 0 := by
      intro x
      have := congrFun hall x
      simpa using this
    have hconst := is_const_of_fderiv_eq_zero (hs.differentiable (by simp)) hz
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨x0, hx0⟩ : ∃ x0, x0 ∉ tsupport g := by
      by_contra h
      push Not at h
      exact (HasCompactSupport.isCompact hc).ne_univ (Set.eq_univ_of_forall h)
    have hg0 : ∀ x, g x = 0 := fun x => (hconst x x0).trans
      (image_eq_zero_of_notMem_tsupport hx0)
    simp [hg0] at hu
  · exact h0

/-- **`L:spatial-fourier-bound`** (TeX lines 101-111), the deterministic Fourier
bound under `H:homog`: for every covariance
satisfying `H:homog` (`HomogHypothesis.HomogCovariance`, including `Γ = 0` and
singular covariances; no `Γ ≠ 0` is needed or assumed) and every real unit
`g ∈ C_c^∞(ℝ^d)`: `b(g) > 0`, the autocorrelation of `g²` is `Γ`-integrable,
`|ĝ²|²` and `(1+|ξ|²)^{-1}` are `μ`-integrable,
`A_sp(g) = ∫ |ĝ²|² dμ ≥ 0`, and `A_sp(g) ≤ 2^{1+α} R_Γ(1) b(g)^{α/2}`.
The constant is `R_Γ(1)`; the lemma's `R_α` of `E:intro-spectral-mass`
equals it by TeX lines 149-155, an identity not formalized here.
Hence `R(g) = A_sp(g)/b(g)^{α/2} ≤ 2^{1+α} R_Γ(1)` (see
`SpatialSmoothRatio.R0_pos_finite`), which is how the manuscript proves
"`R_0` finite" of `P:spatial-smooth-ratio` (lines 185-188), independently of
`T:full-upper`. -/
theorem spatial_fourier_bound_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) {g : Rd d → ℝ} (hg : IsUnitTest g) :
    0 < gradEnergy g ∧
      Integrable (autocorr (fun x => g x ^ 2)) Γ ∧
      Integrable (fun ξ => ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2) μ ∧
      Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ ∧
      spatialEnergy Γ g = ∫ ξ, ‖fourierQ (fun x => g x ^ 2) ξ‖ ^ 2 ∂μ ∧
      0 ≤ spatialEnergy Γ g ∧
      spatialEnergy Γ g ≤
        2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1 * gradEnergy g ^ (alpha / 2) := by
  have hd : 0 < d := by rcases hH.dim with h | h | h <;> omega
  have := hH.Γ_radon
  have := hH.μ_radon
  have ha2 : alpha < 2 := by linarith [hH.threshold, hH.alpha0_pos]
  have hb := gradEnergy_pos hd hg
  exact ⟨hb, spatial_fourier_bound hH.spectral
    (MaskedSpectralGrowth.spectralHomogeneous_of_homog hH) ha2 hg hb⟩

end StratonovichHAMSecondMoment.SpatialFourierBound
