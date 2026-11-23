module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-A1 (approved by Le on 2026-11-20): `L:uniform-mean-cutoff`
(`integrated_uniform_mean.tex`, statement lines 40-53, proof lines 55-73, at revision edf7085f
(book 1.1.3)) against the frozen interface `CameronInterface` (dev commit 1e9c544;
nothing there is changed).

Main results (the A1 list of `docs/l16/INTERFACE.md`, with the frozen target names):
* `uniform_cutoff (η) : UniformCutoffTarget η`: for every real `σ` and `R ≥ 1`, multiplication
  by `η_R` on `H^σ` exists as a bounded operator of norm at most `M_σ` (`Msigma η σ`);
* `sobolev_embed : SobolevEmbedTarget d`: `H^s ↪ H^t` (`t ≤ s`) has norm at most one;
* `uniform_spatial_mean (S) : UniformSpatialMeanTarget S`: `E:uniform-spatial-mean`, the row
  bound `‖k_R(z,w)‖ ≤ A M² ‖z‖ ‖w‖` and `‖T_R‖ ≤ A M²` for every `T_R` with that row.

Lean proof route (TeX lines 55-73):
* With Mathlib's `𝓕` (kernel `e^{-2πi⟪x,ξ⟫}`), Fourier inversion of `η` and Fubini give
  `𝓕(η_R φ)(ξ) = ∫ 𝓕η(p) 𝓕φ(ξ - p/R) dp` (`fourier_etaR_mul`); this is the TeX's convolution
  with `η̂_R(q) = R^d η̂(Rq)` after the substitution `p = Rq`, done before any estimate.
* Peetre's inequality `⟨a⟩^σ ≤ 2^{|σ|/2} ⟨a-b⟩^{|σ|} ⟨b⟩^σ` (`weight_peetre`, with
  `⟨x⟩² = 1 + |2πx|²`) and `⟨p/R⟩ ≤ ⟨p⟩` (`R ≥ 1`) bound the weighted transform pointwise by
  `∫ k(p) G(ξ - p/R) dp`, `k = 2^{|σ|/2}|𝓕η|⟨·⟩^{|σ|}`, `G = ⟨·⟩^σ |𝓕φ|`.
* The `L¹ * L²` inequality is proved in `ℝ≥0∞` by Cauchy-Schwarz in `p` (`sq_lintegral_mul_le`)
  and Tonelli with translation invariance; `∫ k = M_σ` (the conversion of the unitary `η̂` to
  Mathlib's `𝓕` is in the docstring of `Msigma`).  This proves the bound on tests
  (`norm_coord_etaR_mul_le`).
* Extension: the bounded map on the test classes extends to the closure of the test classes
  (`LinearMap.extendOfNorm`) and is composed with the orthogonal projection onto that closure
  (`exists_ext_of_bound`), which has norm at most one.  The TeX's "density extends it to
  `H^σ`" is thereby not needed for the existence and the bound at every real `σ`; at
  `σ = ±1/2` the tests are dense (`UniformMeanFoundation`), so there the operator is the unique
  one.  The same extension gives the embedding `H^s ↪ H^t` from `‖φ‖_{H^t} ≤ ‖φ‖_{H^s}`.
* `E:uniform-spatial-mean`: `‖ι‖ ≤ 1`, `‖L_η‖ ≤ M`, the product bound `A`, and the two
  component bounds `‖z₁‖, ‖z₂‖ ≤ ‖z‖_E` (the map `w₂ ↦ Λ⁻¹ w₂` is the identity of
  coordinates `lam.symm`); the operator bound is Cauchy-Schwarz in `H_sp` at `w = T_R q z`.

No `sorry`, no axiom; every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`.  Lemmas whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff RealInnerProductSpace Real SchwartzMap

namespace StratonovichHAMSecondMoment.UniformMeanCutoff

open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)
open OccupationCompletion (SpData Hsp)
open UniformMeanInterface
open CameronInterface

variable {d : ℕ}

/-! ### The weight `⟨x⟩² = 1 + |2πx|²` and Peetre's inequality -/

/-- Auxiliary: the squared Japanese bracket `⟨x⟩² = 1 + |2πx|²` (Mathlib frequency `x`). -/
def Wt (x : Rd d) : ℝ := 1 + ‖(2 * π) • x‖ ^ 2

/-- Auxiliary: `⟨x⟩² ≥ 1`. -/
theorem one_le_Wt (x : Rd d) : 1 ≤ Wt x := by
  unfold Wt; nlinarith [norm_nonneg ((2 * π) • x)]

/-- Auxiliary: `⟨x⟩² > 0`. -/
theorem Wt_pos (x : Rd d) : 0 < Wt x := lt_of_lt_of_le one_pos (one_le_Wt x)

/-- Auxiliary: `⟨-x⟩ = ⟨x⟩`, in the form `⟨b - a⟩ = ⟨a - b⟩`. -/
theorem Wt_sub_comm (a b : Rd d) : Wt (b - a) = Wt (a - b) := by
  unfold Wt; rw [← neg_sub, smul_neg, norm_neg]

/-- **Quadratic Peetre inequality**: `⟨a⟩² ≤ 2 ⟨a - b⟩² ⟨b⟩²`. -/
theorem quad_peetre (a b : Rd d) : Wt a ≤ 2 * Wt (a - b) * Wt b := by
  unfold Wt
  have h : ‖(2 * π) • a‖ ≤ ‖(2 * π) • (a - b)‖ + ‖(2 * π) • b‖ := by
    calc ‖(2 * π) • a‖ = ‖(2 * π) • (a - b) + (2 * π) • b‖ := by
          rw [← smul_add, sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hX := norm_nonneg ((2 * π) • (a - b))
  have hY := norm_nonneg ((2 * π) • b)
  have hZ := norm_nonneg ((2 * π) • a)
  have h2 : ‖(2 * π) • a‖ ^ 2 ≤ (‖(2 * π) • (a - b)‖ + ‖(2 * π) • b‖) ^ 2 :=
    pow_le_pow_left₀ hZ h 2
  nlinarith [sq_nonneg (‖(2 * π) • (a - b)‖ - ‖(2 * π) • b‖),
    mul_nonneg (sq_nonneg ‖(2 * π) • (a - b)‖) (sq_nonneg ‖(2 * π) • b‖)]

/-- **Peetre's inequality** (`integrated_uniform_mean.tex` lines 56-59 at revision edf7085f
(book 1.1.3)): `⟨a⟩^σ ≤ 2^{|σ|/2} ⟨a-b⟩^{|σ|} ⟨b⟩^σ` for every real `σ`. -/
theorem weight_peetre (σ : ℝ) (a b : Rd d) :
    Wt a ^ (σ / 2) ≤ 2 ^ (|σ| / 2) * Wt (a - b) ^ (|σ| / 2) * Wt b ^ (σ / 2) := by
  have ha := Wt_pos a
  have hb := Wt_pos b
  have hab := Wt_pos (a - b)
  rcases le_or_gt 0 σ with hσ | hσ
  · rw [abs_of_nonneg hσ]
    have hs : 0 ≤ σ / 2 := by linarith
    calc Wt a ^ (σ / 2) ≤ (2 * Wt (a - b) * Wt b) ^ (σ / 2) :=
          Real.rpow_le_rpow ha.le (quad_peetre a b) hs
      _ = _ := by
        rw [Real.mul_rpow (by positivity) hb.le, Real.mul_rpow (by norm_num) hab.le]
  · rw [abs_of_neg hσ]
    set τ : ℝ := -σ / 2 with hτ
    have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
    have key : Wt b ^ τ ≤ 2 ^ τ * Wt (a - b) ^ τ * Wt a ^ τ := by
      calc Wt b ^ τ ≤ (2 * Wt (b - a) * Wt a) ^ τ :=
            Real.rpow_le_rpow hb.le (quad_peetre b a) hτ0
        _ = _ := by
          rw [Wt_sub_comm, Real.mul_rpow (by positivity) ha.le,
            Real.mul_rpow (by norm_num) hab.le]
    have hA : 0 < Wt a ^ τ := Real.rpow_pos_of_pos ha τ
    have hB : 0 < Wt b ^ τ := Real.rpow_pos_of_pos hb τ
    have e1 : σ / 2 = -τ := by rw [hτ]; ring
    rw [e1, Real.rpow_neg ha.le, Real.rpow_neg hb.le, ← div_eq_mul_inv, le_div_iff₀ hB,
      inv_mul_le_iff₀ hA]
    linarith

/-- Auxiliary: `⟨p/R⟩ ≤ ⟨p⟩` for `R ≥ 1`, raised to a nonnegative power. -/
theorem Wt_inv_smul_rpow_le {R : ℝ} (hR : 1 ≤ R) (p : Rd d) {t : ℝ} (ht : 0 ≤ t) :
    Wt (R⁻¹ • p) ^ t ≤ Wt p ^ t := by
  refine Real.rpow_le_rpow (Wt_pos _).le ?_ ht
  unfold Wt
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have e : ‖(2 * π) • (R⁻¹ • p)‖ = R⁻¹ * ‖(2 * π) • p‖ := by
    rw [smul_comm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
  rw [e]
  have h1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have h0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have hn := norm_nonneg ((2 * π) • p)
  have : R⁻¹ * ‖(2 * π) • p‖ ≤ ‖(2 * π) • p‖ := by nlinarith
  nlinarith [mul_nonneg h0 hn]

/-! ### The Fourier transform of `η_R φ` -/

/-- Auxiliary: the profile `η` is a test function. -/
theorem eta_isTest (η : CutoffProfile d) : IsTestFunction η.η :=
  ⟨η.smooth, (isCompact_closedBall (0 : Rd d) 2).of_isClosed_subset (isClosed_tsupport _)
    η.support_subset⟩

/-- Auxiliary: `η_R φ` is a test function. -/
theorem etaR_mul_isTest (η : CutoffProfile d) (R : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    IsTestFunction fun x => etaR η R x * φ x :=
  isTest_smooth_mul (PositiveRawMean.etaR_contDiff η R) hφ

/-- Auxiliary: Fourier inversion for the profile, `η(y) = ∫ e^{2πi⟪p,y⟫} 𝓕η(p) dp`. -/
theorem eta_inversion (η : CutoffProfile d) (y : Rd d) :
    (η.η y : ℂ) = ∫ p, 𝐞 ⟪p, y⟫ • 𝓕 (fun x => (η.η x : ℂ)) p := by
  set hS : 𝓢(Rd d, ℂ) := H1Mathlib.testSchwartz (eta_isTest η)
  have h0 : 𝓕⁻ (𝓕 hS : 𝓢(Rd d, ℂ)) = hS := fourierInv_fourier_eq hS
  have h : (𝓕⁻ (𝓕 hS : 𝓢(Rd d, ℂ)) : 𝓢(Rd d, ℂ)) y = hS y := by rw [h0]
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq] at h
  exact h.symm

/-- Auxiliary: the integrand of the convolution formula. -/
def convIntegrand (η : CutoffProfile d) (R : ℝ) (φ : Rd d → ℝ) (ξ : Rd d) (x p : Rd d) : ℂ :=
  𝐞 (-⟪x, ξ - R⁻¹ • p⟫) • (𝓕 (fun x => (η.η x : ℂ)) p * (φ x : ℂ))

/-- Auxiliary: the phase identity `-⟪x,ξ⟫ + ⟪p, x/R⟫ = -⟪x, ξ - p/R⟫`. -/
theorem phase_eq (R : ℝ) (x ξ p : Rd d) :
    -⟪x, ξ⟫ + ⟪p, R⁻¹ • x⟫ = -⟪x, ξ - R⁻¹ • p⟫ := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm p x]
  ring

/-- Auxiliary: the integrand is integrable on the product. -/
theorem integrable_convIntegrand (η : CutoffProfile d) (R : ℝ) {φ : Rd d → ℝ}
    (hφ : IsTestFunction φ) (ξ : Rd d) :
    Integrable (Function.uncurry (convIntegrand η R φ ξ))
      ((volume : Measure (Rd d)).prod volume) := by
  have hφi : Integrable (fun x => (φ x : ℂ)) (volume : Measure (Rd d)) :=
    (H1Mathlib.testSchwartz hφ).integrable
  have hηi : Integrable (𝓕 (fun x => (η.η x : ℂ))) (volume : Measure (Rd d)) :=
    (𝓕 (H1Mathlib.testSchwartz (eta_isTest η))).integrable
  have hprod := hφi.mul_prod hηi
  refine hprod.norm.mono' ?_ (Eventually.of_forall fun z => ?_)
  · have hc1 : Continuous fun z : Rd d × Rd d => 𝐞 (-⟪z.1, ξ - R⁻¹ • z.2⟫) :=
      Real.continuous_fourierChar.comp (by fun_prop)
    have hc2 : Continuous fun z : Rd d × Rd d => 𝓕 (fun x => (η.η x : ℂ)) z.2 :=
      (𝓕 (H1Mathlib.testSchwartz (eta_isTest η))).continuous.comp continuous_snd
    have hc3 : Continuous fun z : Rd d × Rd d => (φ z.1 : ℂ) :=
      (H1Mathlib.testSchwartz hφ).continuous.comp continuous_fst
    exact (hc1.smul (hc2.mul hc3)).aestronglyMeasurable
  · simp only [Function.uncurry, convIntegrand, Circle.norm_smul]
    rw [mul_comm]

/-- **The Fourier transform of `η_R φ`** (`integrated_uniform_mean.tex` lines 56-63 at revision
edf7085f (book 1.1.3): the convolution bound 56-61, with `η̂_R(q) = R^d η̂(Rq)` and the
substitution `p = Rq` at 62-63):
`𝓕(η_R φ)(ξ) = ∫ 𝓕η(p) 𝓕φ(ξ - p/R) dp`. -/
theorem fourier_etaR_mul (η : CutoffProfile d) (R : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ)
    (ξ : Rd d) :
    𝓕 (fun x => ((etaR η R x * φ x : ℝ) : ℂ)) ξ =
      ∫ p, 𝓕 (fun x => (η.η x : ℂ)) p * 𝓕 (fun x => (φ x : ℂ)) (ξ - R⁻¹ • p) := by
  have hA : ∀ x, 𝐞 (-⟪x, ξ⟫) • ((etaR η R x * φ x : ℝ) : ℂ) =
      ∫ p, convIntegrand η R φ ξ x p := by
    intro x
    rw [Complex.ofReal_mul, etaR, eta_inversion η (R⁻¹ • x), ← integral_mul_const,
      Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [convIntegrand, Circle.smul_def, smul_eq_mul]
    rw [← phase_eq R x ξ p, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have hB : ∀ p, ∫ x, convIntegrand η R φ ξ x p =
      𝓕 (fun x => (η.η x : ℂ)) p * 𝓕 (fun x => (φ x : ℂ)) (ξ - R⁻¹ • p) := by
    intro p
    rw [Real.fourier_eq (fun x => (φ x : ℂ)) (ξ - R⁻¹ • p), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [convIntegrand]
    rw [mul_smul_comm]
  calc 𝓕 (fun x => ((etaR η R x * φ x : ℝ) : ℂ)) ξ
      = ∫ x, ∫ p, convIntegrand η R φ ξ x p := by
        rw [Real.fourier_eq]
        exact integral_congr_ae (Eventually.of_forall hA)
    _ = ∫ p, ∫ x, convIntegrand η R φ ξ x p :=
        integral_integral_swap (integrable_convIntegrand η R hφ ξ)
    _ = _ := integral_congr_ae (Eventually.of_forall hB)

/-! ### The `L¹ * L²` bound in `ℝ≥0∞` -/

/-- Auxiliary: Cauchy-Schwarz with a weight, `(∫ k g)² ≤ (∫ k) (∫ k g²)` in `ℝ≥0∞`. -/
theorem sq_lintegral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {k g : α → ℝ≥0∞}
    (hk : AEMeasurable k μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, k a * g a ∂μ) ^ 2 ≤ (∫⁻ a, k a ∂μ) * ∫⁻ a, k a * g a ^ 2 ∂μ := by
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  have hsq' : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, Nat.cast_ofNat, hsq]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun a => k a ^ (1 / 2 : ℝ)) (g := fun a => k a ^ (1 / 2 : ℝ) * g a)
    (hk.pow_const _) ((hk.pow_const _).mul hg)
  have e1 : ∀ a, (fun a => k a ^ (1 / 2 : ℝ)) a * (fun a => k a ^ (1 / 2 : ℝ) * g a) a =
      k a * g a := fun a => by
    simp only
    rw [← mul_assoc, ← sq, hsq']
  have e2 : ∀ a, (fun a => k a ^ (1 / 2 : ℝ) * g a) a ^ (2 : ℝ) = k a * g a ^ 2 := fun a => by
    simp only
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq, ← ENNReal.rpow_natCast,
      Nat.cast_ofNat]
  simp only [Pi.mul_apply, e1, e2, hsq] at h
  calc (∫⁻ a, k a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, k a ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, k a * g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = _ := by rw [mul_pow, hsq', hsq']

/-! ### The cutoff bound on tests -/

/-- Auxiliary: `‖⟨2πξ⟩^σ‖ = ⟨2πξ⟩^σ` for the complex weight. -/
theorem norm_msWeight (σ : ℝ) (ξ : Rd d) : ‖msWeight σ ξ‖ = Wt ξ ^ (σ / 2) := by
  rw [msWeight, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Real.rpow_nonneg (Wt_pos ξ).le _)

/-- Auxiliary: `ξ ↦ |𝓕η(ξ)| ⟨2πξ⟩^{|σ|}` is integrable (it is the norm of a Schwartz
function). -/
theorem integrable_Msigma_integrand (η : CutoffProfile d) (σ : ℝ) :
    Integrable (fun ξ : Rd d => ‖𝓕 (fun x => (η.η x : ℂ)) ξ‖ *
      (1 + ‖(2 * π) • ξ‖ ^ 2) ^ (|σ| / 2)) (volume : Measure (Rd d)) := by
  refine (coordSchwartz |σ| (eta_isTest η)).integrable.norm.congr
    (Eventually.of_forall fun ξ => ?_)
  simp only [coordSchwartz, SchwartzMap.smulLeftCLM_apply_apply (msWeight_growth _),
    smul_eq_mul, norm_mul, norm_msWeight, SchwartzMap.fourier_coe]
  rw [mul_comm]; rfl

/-- Auxiliary: `M_σ ≥ 0`. -/
theorem Msigma_nonneg (η : CutoffProfile d) (σ : ℝ) : 0 ≤ Msigma η σ :=
  mul_nonneg (by positivity) (integral_nonneg fun ξ =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))

/-- Auxiliary: `ofReal ‖coord σ φ‖² = ∫⁻ (⟨2πξ⟩^σ |𝓕φ(ξ)|)²`. -/
theorem ofReal_norm_coord_sq (σ : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ENNReal.ofReal (‖coord σ φ‖ ^ 2) =
      ∫⁻ ξ, (ENNReal.ofReal (Wt ξ ^ (σ / 2)) * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ₑ) ^ 2 := by
  rw [norm_coord_sq σ hφ, ofReal_integral_eq_lintegral_ofReal (integrable_weighted σ hφ)
    (Eventually.of_forall fun ξ => mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (sq_nonneg _))]
  refine lintegral_congr fun ξ => ?_
  have hW : (1 + ‖(2 * π) • ξ‖ ^ 2) ^ σ = (Wt ξ ^ (σ / 2)) ^ 2 := by
    show (1 + ‖(2 * π) • ξ‖ ^ 2) ^ σ = ((1 + ‖(2 * π) • ξ‖ ^ 2) ^ (σ / 2)) ^ 2
    rw [← Real.rpow_natCast ((1 + ‖(2 * π) • ξ‖ ^ 2) ^ (σ / 2)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hW, ← mul_pow, ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg (Wt_pos ξ).le _)
    (norm_nonneg _)), ENNReal.ofReal_mul (Real.rpow_nonneg (Wt_pos ξ).le _),
    ofReal_norm, SchwartzMap.fourier_coe]
  rfl

/-- **The cutoff bound on tests** (`L:uniform-mean-cutoff`, `integrated_uniform_mean.tex`
lines 41-46, proof lines 56-63, at revision edf7085f (book 1.1.3)):
`‖η_R φ‖_{H^σ} ≤ M_σ ‖φ‖_{H^σ}` for every real `σ`, every `R ≥ 1` and every real test `φ`. -/
theorem norm_coord_etaR_mul_le (η : CutoffProfile d) (σ : ℝ) {R : ℝ} (hR : 1 ≤ R)
    {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ‖coord σ (fun x => etaR η R x * φ x)‖ ≤ Msigma η σ * ‖coord σ φ‖ := by
  have hψ := etaR_mul_isTest η R hφ
  set Fη : Rd d → ℂ := 𝓕 (fun x => (η.η x : ℂ)) with hFη
  set Fφ : Rd d → ℂ := 𝓕 (fun x => (φ x : ℂ)) with hFφ
  set Fψ : Rd d → ℂ := 𝓕 (fun x => ((etaR η R x * φ x : ℝ) : ℂ)) with hFψ
  have hcFη : Continuous Fη := (𝓕 (H1Mathlib.testSchwartz (eta_isTest η))).continuous
  have hcFφ : Continuous Fφ := (𝓕 (H1Mathlib.testSchwartz hφ)).continuous
  have hcWt : Continuous (Wt (d := d)) := by unfold Wt; fun_prop
  set G : Rd d → ℝ≥0∞ := fun ζ => ENNReal.ofReal (Wt ζ ^ (σ / 2)) * ‖Fφ ζ‖ₑ with hG
  set K : Rd d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (2 ^ (|σ| / 2) * Wt p ^ (|σ| / 2)) * ‖Fη p‖ₑ with hK
  have hGm : Measurable G := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul (continuous_enorm.comp hcFφ).measurable
    exact (hcWt.rpow_const fun ζ => Or.inl (Wt_pos ζ).ne').measurable
  have hKm : Measurable K := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul (continuous_enorm.comp hcFη).measurable
    exact (continuous_const.mul
      (hcWt.rpow_const fun ζ => Or.inl (Wt_pos ζ).ne')).measurable
  have hk0 : ∀ p : Rd d, 0 ≤ 2 ^ (|σ| / 2) * Wt p ^ (|σ| / 2) := fun p =>
    mul_nonneg (by positivity) (Real.rpow_nonneg (Wt_pos p).le _)
  -- `∫ K = M_σ`
  have hKint : ∫⁻ p, K p = ENNReal.ofReal (Msigma η σ) := by
    rw [Msigma, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
      ((integrable_Msigma_integrand η σ).const_mul _)
      (Eventually.of_forall fun ξ => mul_nonneg (by positivity)
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)))]
    refine lintegral_congr fun p => ?_
    simp only [hK]
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (hk0 p)]
    congr 1
    show _ = 2 ^ (|σ| / 2) * (‖Fη p‖ * Wt p ^ (|σ| / 2))
    ring
  -- pointwise bound
  have hpt : ∀ ξ, ENNReal.ofReal (Wt ξ ^ (σ / 2)) * ‖Fψ ξ‖ₑ ≤
      ∫⁻ p, K p * G (ξ - R⁻¹ • p) := by
    intro ξ
    have h1 : ‖Fψ ξ‖ₑ ≤ ∫⁻ p, ‖Fη p‖ₑ * ‖Fφ (ξ - R⁻¹ • p)‖ₑ := by
      rw [hFψ, fourier_etaR_mul η R hφ ξ]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun p => ?_
      rw [enorm_mul]
    calc ENNReal.ofReal (Wt ξ ^ (σ / 2)) * ‖Fψ ξ‖ₑ
        ≤ ENNReal.ofReal (Wt ξ ^ (σ / 2)) * ∫⁻ p, ‖Fη p‖ₑ * ‖Fφ (ξ - R⁻¹ • p)‖ₑ :=
          by gcongr
      _ = ∫⁻ p, ENNReal.ofReal (Wt ξ ^ (σ / 2)) * (‖Fη p‖ₑ * ‖Fφ (ξ - R⁻¹ • p)‖ₑ) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ p, K p * G (ξ - R⁻¹ • p) := by
          refine lintegral_mono fun p => ?_
          have hw : ENNReal.ofReal (Wt ξ ^ (σ / 2)) ≤
              ENNReal.ofReal (2 ^ (|σ| / 2) * Wt p ^ (|σ| / 2)) *
                ENNReal.ofReal (Wt (ξ - R⁻¹ • p) ^ (σ / 2)) := by
            rw [← ENNReal.ofReal_mul (hk0 p)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hP := weight_peetre σ ξ (ξ - R⁻¹ • p)
            rw [sub_sub_cancel] at hP
            have hm := Wt_inv_smul_rpow_le hR p (show 0 ≤ |σ| / 2 by positivity)
            have h0 := Real.rpow_nonneg (Wt_pos (ξ - R⁻¹ • p)).le (σ / 2)
            have h2 : (0 : ℝ) ≤ 2 ^ (|σ| / 2) := by positivity
            calc Wt ξ ^ (σ / 2)
                ≤ 2 ^ (|σ| / 2) * Wt (R⁻¹ • p) ^ (|σ| / 2) * Wt (ξ - R⁻¹ • p) ^ (σ / 2) := hP
              _ ≤ 2 ^ (|σ| / 2) * Wt p ^ (|σ| / 2) * Wt (ξ - R⁻¹ • p) ^ (σ / 2) := by gcongr
          calc ENNReal.ofReal (Wt ξ ^ (σ / 2)) * (‖Fη p‖ₑ * ‖Fφ (ξ - R⁻¹ • p)‖ₑ)
              ≤ ENNReal.ofReal (2 ^ (|σ| / 2) * Wt p ^ (|σ| / 2)) *
                  ENNReal.ofReal (Wt (ξ - R⁻¹ • p) ^ (σ / 2)) *
                    (‖Fη p‖ₑ * ‖Fφ (ξ - R⁻¹ • p)‖ₑ) := by gcongr
            _ = K p * G (ξ - R⁻¹ • p) := by simp only [hK, hG]; ring
  -- the `L¹ * L²` bound
  have hL2 : ∫⁻ ξ, (ENNReal.ofReal (Wt ξ ^ (σ / 2)) * ‖Fψ ξ‖ₑ) ^ 2 ≤
      (∫⁻ p, K p) ^ 2 * ∫⁻ ζ, G ζ ^ 2 := by
    have hmeas : ∀ ξ : Rd d, Measurable fun p => G (ξ - R⁻¹ • p) := fun ξ =>
      hGm.comp (by fun_prop)
    calc ∫⁻ ξ, (ENNReal.ofReal (Wt ξ ^ (σ / 2)) * ‖Fψ ξ‖ₑ) ^ 2
        ≤ ∫⁻ ξ, (∫⁻ p, K p) * ∫⁻ p, K p * G (ξ - R⁻¹ • p) ^ 2 := by
          refine lintegral_mono fun ξ => ?_
          exact (pow_le_pow_left₀ zero_le (hpt ξ) 2).trans
            (sq_lintegral_mul_le hKm.aemeasurable (hmeas ξ).aemeasurable)
      _ = (∫⁻ p, K p) * ∫⁻ ξ, ∫⁻ p, K p * G (ξ - R⁻¹ • p) ^ 2 :=
          lintegral_const_mul' _ _ (by rw [hKint]; exact ENNReal.ofReal_ne_top)
      _ = (∫⁻ p, K p) * ∫⁻ p, ∫⁻ ξ, K p * G (ξ - R⁻¹ • p) ^ 2 := by
          congr 1
          refine lintegral_lintegral_swap ?_
          refine (Measurable.mul (hKm.comp measurable_snd) ?_).aemeasurable
          exact (hGm.comp (by fun_prop)).pow_const 2
      _ = (∫⁻ p, K p) * ∫⁻ p, K p * ∫⁻ ζ, G ζ ^ 2 := by
          congr 1
          refine lintegral_congr fun p => ?_
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)]
          congr 1
          exact lintegral_sub_right_eq_self (fun ζ => G ζ ^ 2) (R⁻¹ • p)
      _ = (∫⁻ p, K p) ^ 2 * ∫⁻ ζ, G ζ ^ 2 := by
          rw [lintegral_mul_const _ hKm, sq, mul_assoc]
  -- back to real norms
  have hfin := ofReal_norm_coord_sq σ hψ
  have hfin' := ofReal_norm_coord_sq σ hφ
  rw [← hFψ] at hfin
  rw [← hFφ] at hfin'
  have hmain : ENNReal.ofReal (‖coord σ (fun x => etaR η R x * φ x)‖ ^ 2) ≤
      ENNReal.ofReal ((Msigma η σ * ‖coord σ φ‖) ^ 2) := by
    rw [hfin, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), hfin', ENNReal.ofReal_pow
      (Msigma_nonneg η σ), ← hKint]
    exact hL2
  have h2 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hmain
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Msigma_nonneg η σ) (norm_nonneg _)) two_ne_zero).mp h2

/-! ### Extension from the test classes -/

/-- Auxiliary: the norm of the class of a test in `H^σ` is that of its coordinate. -/
theorem norm_toHsob (σ : ℝ) (φ : Rd d → ℝ) : ‖toHsob (d := d) σ φ‖ = ‖coord σ φ‖ := rfl

/-- Auxiliary: `φ ↦ [φ]_{H^σ}` on the test subspace. -/
def toHsobL (σ : ℝ) : testSub d →ₗ[ℝ] Hsob d σ where
  toFun φ := toHsob σ (φ : Rd d → ℝ)
  map_add' φ ψ := by
    apply Subtype.ext
    change coord σ ((φ : Rd d → ℝ) + (ψ : Rd d → ℝ)) =
      coord σ (φ : Rd d → ℝ) + coord σ (ψ : Rd d → ℝ)
    exact coord_add σ φ.2 ψ.2
  map_smul' c φ := by
    apply Subtype.ext
    change coord σ (c • (φ : Rd d → ℝ)) = c • coord σ (φ : Rd d → ℝ)
    rw [coord_smul σ c φ.2]; rfl

/-- Auxiliary: `φ ↦ [χ φ]_{H^τ}` on the test subspace, for a smooth `χ`. -/
def mulHsobL (τ : ℝ) (χ : Rd d → ℝ) (hχ : ContDiff ℝ ∞ χ) : testSub d →ₗ[ℝ] Hsob d τ where
  toFun φ := toHsob τ fun x => χ x * (φ : Rd d → ℝ) x
  map_add' φ ψ := by
    apply Subtype.ext
    have e : (fun x => χ x * ((φ + ψ : testSub d) : Rd d → ℝ) x) =
        (fun x => χ x * (φ : Rd d → ℝ) x) + fun x => χ x * (ψ : Rd d → ℝ) x := by
      funext x; simp [mul_add]
    change coord τ (fun x => χ x * ((φ + ψ : testSub d) : Rd d → ℝ) x) =
      coord τ (fun x => χ x * (φ : Rd d → ℝ) x) + coord τ (fun x => χ x * (ψ : Rd d → ℝ) x)
    rw [e, coord_add τ (isTest_smooth_mul hχ φ.2) (isTest_smooth_mul hχ ψ.2)]
  map_smul' c φ := by
    apply Subtype.ext
    have e : (fun x => χ x * ((c • φ : testSub d) : Rd d → ℝ) x) =
        c • fun x => χ x * (φ : Rd d → ℝ) x := by
      funext x; simp; ring
    change coord τ (fun x => χ x * ((c • φ : testSub d) : Rd d → ℝ) x) =
      c • coord τ (fun x => χ x * (φ : Rd d → ℝ) x)
    rw [e, coord_smul τ c (isTest_smooth_mul hχ φ.2)]; rfl

/-- **Bounded extension from the test classes** (the extension step of
`integrated_uniform_mean.tex` lines 64-65 at revision edf7085f (book 1.1.3)): a linear map
on the tests bounded by `C ‖φ‖_{H^σ}` is the restriction of a bounded operator on `H^σ` of norm
at most `C`.  (It is extended to the closure of the test classes and composed with the
orthogonal projection onto that closure; no density of tests in `H^σ` is needed.) -/
theorem exists_ext_of_bound {σ τ : ℝ} (F : testSub d →ₗ[ℝ] Hsob d τ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ φ : testSub d, ‖F φ‖ ≤ C * ‖toHsobL σ φ‖) :
    ∃ L : Hsob d σ →L[ℝ] Hsob d τ, (∀ φ : testSub d, L (toHsobL σ φ) = F φ) ∧ ‖L‖ ≤ C := by
  set V : Submodule ℝ (Hsob d σ) := (LinearMap.range (toHsobL (d := d) σ)).topologicalClosure
    with hV
  have : IsClosed (V : Set (Hsob d σ)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace V := IsClosed.completeSpace_coe
  have hmem : ∀ φ : testSub d, toHsobL σ φ ∈ V := fun φ =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ φ)
  let e : testSub d →ₗ[ℝ] V := (toHsobL σ).codRestrict V hmem
  have he : DenseRange e := by
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro v
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
    have hv : (v : Hsob d σ) ∈ closure (LinearMap.range (toHsobL (d := d) σ) : Set _) := by
      rw [← Submodule.topologicalClosure_coe]; exact v.2
    refine closure_mono ?_ hv
    rintro _ ⟨φ, rfl⟩
    exact ⟨e φ, ⟨φ, rfl⟩, rfl⟩
  have hb : ∀ φ, ‖F φ‖ ≤ C * ‖e φ‖ := hF
  refine ⟨F.extendOfNorm e ∘L V.orthogonalProjectionOnto, fun φ => ?_, ?_⟩
  · have h1 : V.orthogonalProjectionOnto (toHsobL σ φ) = e φ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e φ)
    rw [ContinuousLinearMap.comp_apply, h1]
    exact LinearMap.extendOfNorm_eq he ⟨C, hb⟩ φ
  · calc ‖F.extendOfNorm e ∘L V.orthogonalProjectionOnto‖
        ≤ ‖F.extendOfNorm e‖ * ‖V.orthogonalProjectionOnto‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul (LinearMap.opNorm_extendOfNorm_le he hC hb)
          (Submodule.orthogonalProjectionOnto_norm_le V)
          (norm_nonneg V.orthogonalProjectionOnto) hC
      _ = C := mul_one C

/-! ### The A1 targets -/

/-- **`L:uniform-mean-cutoff`, first sentence** (`integrated_uniform_mean.tex` lines 41-47,
proof lines 56-63, at revision edf7085f (book 1.1.3)): for every real `σ` and every
`R ≥ 1`, multiplication by `η_R` on `H^σ` is a bounded operator of norm at most `M_σ`. -/
theorem uniform_cutoff (η : CutoffProfile d) : UniformCutoffTarget η := by
  intro σ R hR
  obtain ⟨L, hL, hLn⟩ := exists_ext_of_bound (σ := σ)
    (mulHsobL σ (etaR η R) (PositiveRawMean.etaR_contDiff η R)) (Msigma_nonneg η σ)
    (fun φ => norm_coord_etaR_mul_le η σ hR φ.2)
  exact ⟨L, fun φ hφ => hL ⟨φ, hφ⟩, hLn⟩

/-- Auxiliary: `‖φ‖_{H^t} ≤ ‖φ‖_{H^s}` for `t ≤ s` and a real test `φ`. -/
theorem norm_coord_le_of_le {s t : ℝ} (hts : t ≤ s) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ‖coord t φ‖ ≤ ‖coord s φ‖ := by
  have h : ‖coord t φ‖ ^ 2 ≤ ‖coord s φ‖ ^ 2 := by
    rw [norm_coord_sq t hφ, norm_coord_sq s hφ]
    refine integral_mono (integrable_weighted t hφ) (integrable_weighted s hφ) fun ξ => ?_
    have h1 : (1 + ‖(2 * π) • ξ‖ ^ 2) ^ t ≤ (1 + ‖(2 * π) • ξ‖ ^ 2) ^ s :=
      Real.rpow_le_rpow_of_exponent_le (one_le_Wt ξ) hts
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **The embedding `H^s ↪ H^t`, `t ≤ s`, of norm at most one** ("`H^{1/2} ↪ H^s` has norm
one", `integrated_uniform_mean.tex` lines 66-67 at revision edf7085f (book 1.1.3)). -/
theorem sobolev_embed : SobolevEmbedTarget d := by
  intro s t hts
  obtain ⟨ι, hι, hιn⟩ := exists_ext_of_bound (σ := s) (toHsobL (d := d) t) zero_le_one
    (fun φ => by rw [one_mul]; exact norm_coord_le_of_le hts φ.2)
  exact ⟨ι, fun φ hφ => hι ⟨φ, hφ⟩, hιn⟩

/-- Auxiliary: the second component of a state is bounded by the state, `‖z₂‖ ≤ ‖z‖_E`. -/
theorem norm_snd_le (z : E d) : ‖(eEquiv z).2‖ ≤ ‖z‖ := by
  have h : ‖(eEquiv z).2‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← toE_eEquiv z, eEquiv_toE, norm_toE_sq]
    nlinarith [sq_nonneg ‖(eEquiv z).1‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- Auxiliary: the first component of a state is bounded by the state, `‖z₁‖ ≤ ‖z‖_E`. -/
theorem norm_fst_le (z : E d) : ‖(eEquiv z).1‖ ≤ ‖z‖ := by
  calc ‖(eEquiv z).1‖ ≤ ‖toE (eEquiv z).1 (eEquiv z).2‖ := norm_le_norm_toE _ _
    _ = ‖z‖ := by rw [toE_eEquiv]

/-- **`E:uniform-spatial-mean`** (`L:uniform-mean-cutoff`, `integrated_uniform_mean.tex`
lines 47-52, proof lines 63-70, at revision edf7085f (book 1.1.3)): for a product map
with constant `A`, an embedding of norm at most one and a cutoff multiplier of norm at most
`M`, `‖k_R(z,w)‖ ≤ A M² ‖z‖ ‖w‖`, and every `T_R` with the row `⟪T_R q z, w⟫ = ⟪q, k_R(z,w)⟫`
has `‖T_R‖ ≤ A M²` (Hilbert Cauchy-Schwarz). -/
theorem uniform_spatial_mean (S : SpData d) : UniformSpatialMeanTarget S := by
  intro s A M P ι Lη hA hP hι hL
  have hM : 0 ≤ M := (norm_nonneg _).trans hL
  have hx : ∀ x, ‖ι (Lη x)‖ ≤ M * ‖x‖ := fun x =>
    calc ‖ι (Lη x)‖ ≤ ‖ι‖ * ‖Lη x‖ := ι.le_opNorm _
      _ ≤ 1 * (M * ‖x‖) := mul_le_mul hι
          ((Lη.le_opNorm x).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _)))
          (norm_nonneg _) zero_le_one
      _ = M * ‖x‖ := one_mul _
  have hrow : ∀ z w, ‖kRow S P ι Lη z w‖ ≤ A * M ^ 2 * ‖z‖ * ‖w‖ := by
    intro z w
    have h1 : ‖hhalfEquiv (eEquiv z).1‖ ≤ ‖z‖ := by
      rw [LinearIsometryEquiv.norm_map]; exact norm_fst_le z
    have h2 : ‖hhalfEquiv (lam.symm (eEquiv w).2)‖ ≤ ‖w‖ := by
      rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]; exact norm_snd_le w
    have ha := (hx (hhalfEquiv (eEquiv z).1)).trans (mul_le_mul_of_nonneg_left h1 hM)
    have hb := (hx (hhalfEquiv (lam.symm (eEquiv w).2))).trans
      (mul_le_mul_of_nonneg_left h2 hM)
    calc ‖kRow S P ι Lη z w‖
        ≤ A * ‖ι (Lη (hhalfEquiv (eEquiv z).1))‖ *
            ‖ι (Lη (hhalfEquiv (lam.symm (eEquiv w).2)))‖ := hP _ _
      _ ≤ A * (M * ‖z‖) * (M * ‖w‖) := by gcongr
      _ = A * M ^ 2 * ‖z‖ * ‖w‖ := by ring
  refine ⟨hrow, fun T hT => ?_⟩
  have hAM : 0 ≤ A * M ^ 2 := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hAM fun q => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have key : ‖T q z‖ ^ 2 ≤ (A * M ^ 2 * ‖q‖ * ‖z‖) * ‖T q z‖ := by
    rw [← real_inner_self_eq_norm_sq, hT]
    calc ⟪q, kRow S P ι Lη z (T q z)⟫
        ≤ ‖q‖ * ‖kRow S P ι Lη z (T q z)‖ := real_inner_le_norm _ _
      _ ≤ ‖q‖ * (A * M ^ 2 * ‖z‖ * ‖T q z‖) :=
          mul_le_mul_of_nonneg_left (hrow _ _) (norm_nonneg _)
      _ = (A * M ^ 2 * ‖q‖ * ‖z‖) * ‖T q z‖ := by ring
  rcases (norm_nonneg (T q z)).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

end StratonovichHAMSecondMoment.UniformMeanCutoff
