module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-A2 (approved by Le on 2026-11-20): `L:cameron-fractional-products`
(`integrated_cameron_mean.tex`, statement lines 29-42, proof lines 44-99, at revision edf7085f
(book 1.1.3)) against the frozen interface `CameronInterface` (dev commit 1e9c544;
nothing there is changed).

Main result: `cameron_fractional_products (hs : α/4 < s) (hs' : s < 1/2) :
FractionalProductsTarget d α s`.

Lean proof route (TeX lines 44-99; differences recorded):
* Bands (Step 2).  The TeX uses sharp dyadic Fourier bands `D_j`.  Here smooth
  Littlewood-Paley bands `ψ_j` (`lpPsi`, a telescoping partition of unity built from
  `Real.smoothTransition`) are used, so that the band pieces of a real test are (real parts of)
  Schwartz functions, hence `H¹` pairs with their classical gradients.  On the support of `ψ_j`
  the physical frequency `|2πξ|` lies in `(2^{j-1}, 2^{j+1})` (`[0,2)` for `j = 0`); this gives
  `N(f_j)² ≤ 2^{(j+1)α/2} ‖ψ_j 𝓕f‖²` and `‖ψ_j 𝓕f‖² ≤ 2^{2(1-j)s} ‖ψ_j ⟨·⟩^s 𝓕f‖²`, and
  Cauchy-Schwarz over `j` gives `Σ_j N(f_j) ≤ C_s ‖f‖_{H^s}` with
  `C_s² = 2^{α/2+2s} / (1 - 2^{α/2-2s})` (`Cs`; the TeX's `C_s`, line 70, with the smooth bands).
* Step 3 on tests: `|f| ≤ Σ_j |f_j|` pointwise (the band sums converge pointwise, by dominated
  convergence on the Fourier side), the absolute four-linear bound of `P:spatial-four-linear` on
  each band quadruple and Tonelli give `E:cameron-fractional-absolute` for real tests
  (`test_absolute`).
* Rough factors: `E:cameron-fractional-absolute` for physical representatives of arbitrary
  `H^s` elements follows from the test case by Fatou along a.e.-convergent subsequences
  (`phys_absolute`).  The TeX passes to the limit in the band series instead.
* The product map: for tests `‖[fg]‖²_{H_sp} = C₄(f,g,f,g)`, so `E:cameron-fractional-product`
  holds on tests; the map is extended bilinearly from the dense tests (density of tests in
  `H^s`, `s ≤ 1`, from `UniformMeanFoundation`), which also gives uniqueness.
* Pairings: `⟪P u₁ u₂, P u₃ u₄⟫ = C₄(f₁,f₂,f₃,f₄)` by density: true on tests, and both sides
  are continuous along test approximants (the right side by multilinearity and the absolute
  bound for differences).
* `Γ = 0` (allowed by the frozen target): `H_sp` carries the zero form, the pair measure is zero
  and every bound is trivial; it is treated separately in `core_bounds`.

No `sorry`, no axiom; every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`.  Lemmas whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronInterface
public import StratonovichHAMSecondMoment.UniformMeanCutoff
public import StratonovichHAMSecondMoment.H1Density

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff RealInnerProductSpace Real SchwartzMap LineDeriv

namespace StratonovichHAMSecondMoment.CameronProducts

open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (IsTestFunction HasWeakGradient)
open OccupationCompletion (SpData Hsp toHsp)
open OccupationKernelRow (pairMeasure)
open SpatialFourLinear (C4 Rsp Nnorm l2 IsH1Pair SquareBound)
open VariationalFloor (grad)
open UniformMeanInterface
open CameronInterface
open UniformMeanCutoff (Wt one_le_Wt Wt_pos)

variable {d : ℕ}

/-! ### A smooth Littlewood-Paley partition -/

/-- Auxiliary: the base cutoff `χ(ζ) = S((4 - |ζ|²)/3)` (`S` = `Real.smoothTransition`): equal to
one for `|ζ| ≤ 1`, zero for `|ζ| ≥ 2`, radially nonincreasing. -/
def lpChi (ζ : Rd d) : ℝ := Real.smoothTransition ((4 - ‖ζ‖ ^ 2) / 3)

/-- Auxiliary: `χ = 1` on the unit ball. -/
theorem lpChi_one {ζ : Rd d} (h : ‖ζ‖ ≤ 1) : lpChi ζ = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  nlinarith [norm_nonneg ζ]

/-- Auxiliary: `χ = 0` outside the radius-two ball. -/
theorem lpChi_zero {ζ : Rd d} (h : 2 ≤ ‖ζ‖) : lpChi ζ = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  rw [div_nonpos_iff]; right
  exact ⟨by nlinarith, by norm_num⟩

/-- Auxiliary: `χ` is radially nonincreasing. -/
theorem lpChi_anti {ζ ζ' : Rd d} (h : ‖ζ‖ ≤ ‖ζ'‖) : lpChi ζ' ≤ lpChi ζ := by
  refine Real.smoothTransition.monotone ?_
  have : ‖ζ‖ ^ 2 ≤ ‖ζ'‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  linarith

/-- Auxiliary: `χ ≥ 0`. -/
theorem lpChi_nonneg (ζ : Rd d) : 0 ≤ lpChi ζ := Real.smoothTransition.nonneg _

/-- Auxiliary: `χ ≤ 1`. -/
theorem lpChi_le_one (ζ : Rd d) : lpChi ζ ≤ 1 := Real.smoothTransition.le_one _

/-- Auxiliary: `χ` is smooth. -/
theorem lpChi_contDiff : ContDiff ℝ ∞ (lpChi (d := d)) := by
  unfold lpChi
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const 3)

/-- Auxiliary: the dyadic cutoff `S_J(ξ) = χ(2^{-J} · 2πξ)` (Mathlib frequency `ξ`). -/
def lpS (J : ℕ) (ξ : Rd d) : ℝ := lpChi (((2 : ℝ) ^ J)⁻¹ • ((2 * π) • ξ))

/-- Auxiliary: `|2^{-J} 2πξ| = |2πξ| / 2^J`. -/
theorem norm_scale (J : ℕ) (ξ : Rd d) :
    ‖((2 : ℝ) ^ J)⁻¹ • ((2 * π) • ξ)‖ = ‖(2 * π) • ξ‖ / 2 ^ J := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_eq_div]

/-- Auxiliary: `S_J = 1` for `|2πξ| ≤ 2^J`. -/
theorem lpS_one {J : ℕ} {ξ : Rd d} (h : ‖(2 * π) • ξ‖ ≤ 2 ^ J) : lpS J ξ = 1 := by
  refine lpChi_one ?_
  rw [norm_scale, div_le_one (by positivity)]; exact h

/-- Auxiliary: `S_J = 0` for `|2πξ| ≥ 2^{J+1}`. -/
theorem lpS_zero {J : ℕ} {ξ : Rd d} (h : 2 ^ (J + 1) ≤ ‖(2 * π) • ξ‖) : lpS J ξ = 0 := by
  refine lpChi_zero ?_
  rw [norm_scale, le_div_iff₀ (by positivity)]
  rw [pow_succ] at h; linarith

/-- Auxiliary: `S_J ≤ S_{J+1}`. -/
theorem lpS_mono (J : ℕ) (ξ : Rd d) : lpS J ξ ≤ lpS (J + 1) ξ := by
  refine lpChi_anti ?_
  rw [norm_scale, norm_scale]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    (pow_le_pow_right₀ (by norm_num) (Nat.le_succ J))

/-- Auxiliary: `S_J ≥ 0`. -/
theorem lpS_nonneg (J : ℕ) (ξ : Rd d) : 0 ≤ lpS J ξ := lpChi_nonneg _

/-- Auxiliary: `S_J ≤ 1`. -/
theorem lpS_le_one (J : ℕ) (ξ : Rd d) : lpS J ξ ≤ 1 := lpChi_le_one _

/-- Auxiliary: `S_J` is smooth. -/
theorem lpS_contDiff (J : ℕ) : ContDiff ℝ ∞ (lpS (d := d) J) :=
  lpChi_contDiff.comp ((contDiff_const_smul _).comp (contDiff_const_smul _))

/-- Auxiliary: `S_J` has compact support. -/
theorem lpS_hasCompactSupport (J : ℕ) : HasCompactSupport (lpS (d := d) J) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) (2 ^ (J + 1))) fun ξ hξ => ?_
  refine lpS_zero ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hp : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  nlinarith [norm_nonneg ξ]

/-- **The Littlewood-Paley bands** `ψ_0 = S_0`, `ψ_j = S_j - S_{j-1}` (`j ≥ 1`): smooth
replacements for the sharp bands `D_j` of `integrated_cameron_mean.tex` lines 63-64 at revision
edf7085f (book 1.1.3). -/
def lpPsi (j : ℕ) (ξ : Rd d) : ℝ := if j = 0 then lpS 0 ξ else lpS j ξ - lpS (j - 1) ξ

/-- Auxiliary: `ψ_{j+1} = S_{j+1} - S_j`. -/
theorem lpPsi_succ (j : ℕ) (ξ : Rd d) : lpPsi (j + 1) ξ = lpS (j + 1) ξ - lpS j ξ := by
  simp [lpPsi]

/-- Auxiliary: `ψ_0 = S_0`. -/
theorem lpPsi_zero_eq : lpPsi (d := d) 0 = lpS 0 := funext fun ξ => by simp [lpPsi]

/-- Auxiliary: telescoping, `Σ_{j ≤ J} ψ_j = S_J`. -/
theorem sum_range_lpPsi (J : ℕ) (ξ : Rd d) :
    ∑ j ∈ Finset.range (J + 1), lpPsi j ξ = lpS J ξ := by
  induction J with
  | zero => simp [lpPsi]
  | succ J ih => rw [Finset.sum_range_succ, ih, lpPsi_succ]; ring

/-- Auxiliary: `ψ_j ≥ 0`. -/
theorem lpPsi_nonneg (j : ℕ) (ξ : Rd d) : 0 ≤ lpPsi j ξ := by
  rcases j with _ | j
  · simp only [lpPsi, ite_true]; exact lpChi_nonneg _
  · rw [lpPsi_succ]; linarith [lpS_mono j ξ]

/-- Auxiliary: `ψ_j ≤ 1`. -/
theorem lpPsi_le_one (j : ℕ) (ξ : Rd d) : lpPsi j ξ ≤ 1 := by
  rcases j with _ | j
  · simp only [lpPsi, ite_true]; exact lpChi_le_one _
  · rw [lpPsi_succ]; linarith [lpChi_le_one (d := d) (((2 : ℝ) ^ (j + 1))⁻¹ • ((2 * π) • ξ)),
      lpChi_nonneg (d := d) (((2 : ℝ) ^ j)⁻¹ • ((2 * π) • ξ)),
      show lpS (j + 1) ξ = lpChi _ from rfl,
      show lpS j ξ = lpChi _ from rfl]

/-- Auxiliary: `Σ_{j < J} ψ_j ≤ 1`. -/
theorem sum_range_lpPsi_le_one (J : ℕ) (ξ : Rd d) :
    ∑ j ∈ Finset.range J, lpPsi j ξ ≤ 1 := by
  rcases J with _ | J
  · simp
  · rw [sum_range_lpPsi]; exact lpChi_le_one _

/-- Auxiliary: `ψ_j` is smooth. -/
theorem lpPsi_contDiff (j : ℕ) : ContDiff ℝ ∞ (lpPsi (d := d) j) := by
  rcases j with _ | j
  · rw [lpPsi_zero_eq]; exact lpS_contDiff 0
  · have : lpPsi (d := d) (j + 1) = fun ξ => lpS (j + 1) ξ - lpS j ξ := funext (lpPsi_succ j)
    rw [this]; exact (lpS_contDiff _).sub (lpS_contDiff _)

/-- Auxiliary: `ψ_j` has compact support. -/
theorem lpPsi_hasCompactSupport (j : ℕ) : HasCompactSupport (lpPsi (d := d) j) := by
  rcases j with _ | j
  · rw [lpPsi_zero_eq]; exact lpS_hasCompactSupport 0
  · have : lpPsi (d := d) (j + 1) = fun ξ => lpS (j + 1) ξ - lpS j ξ := funext (lpPsi_succ j)
    rw [this]; exact (lpS_hasCompactSupport _).sub (lpS_hasCompactSupport _)

/-- Auxiliary: the complexified band has temperate growth. -/
theorem lpPsiC_growth (j : ℕ) : (fun ξ : Rd d => (lpPsi j ξ : ℂ)).HasTemperateGrowth :=
  HasCompactSupport.hasTemperateGrowth ((lpPsi_hasCompactSupport j).comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (lpPsi_contDiff j))

/-- Auxiliary: on the support of `ψ_j`, `|2πξ| < 2^{j+1}`. -/
theorem lpPsi_high {j : ℕ} {ξ : Rd d} (h : lpPsi j ξ ≠ 0) : ‖(2 * π) • ξ‖ < 2 ^ (j + 1) := by
  by_contra hc
  rw [not_lt] at hc
  apply h
  rcases j with _ | j
  · simp only [lpPsi, ite_true]; exact lpS_zero hc
  · rw [lpPsi_succ, lpS_zero hc, lpS_zero (le_trans (pow_le_pow_right₀ (by norm_num)
      (Nat.le_succ _)) hc)]
    norm_num

/-- Auxiliary: on the support of `ψ_j`, `j ≥ 1`, `|2πξ| > 2^{j-1}`. -/
theorem lpPsi_low {j : ℕ} {ξ : Rd d} (h : lpPsi (j + 1) ξ ≠ 0) : 2 ^ j < ‖(2 * π) • ξ‖ := by
  by_contra hc
  rw [not_lt] at hc
  apply h
  rw [lpPsi_succ, lpS_one hc, lpS_one (le_trans hc (pow_le_pow_right₀ (by norm_num)
    (Nat.le_succ _)))]
  norm_num

/-- Auxiliary: the dyadic cutoffs tend to one. -/
theorem tendsto_lpS (ξ : Rd d) : Tendsto (fun J => lpS J ξ) atTop (𝓝 1) := by
  obtain ⟨J0, hJ0⟩ := pow_unbounded_of_one_lt ‖(2 * π) • ξ‖ (by norm_num : (1 : ℝ) < 2)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop J0] with J hJ
  exact (lpS_one (hJ0.le.trans (pow_le_pow_right₀ (by norm_num) hJ))).symm

/-- Auxiliary: on the support of `ψ_j`, `⟨2πξ⟩² ≥ 2^{2(j-1)}` (all `j`). -/
theorem lpPsi_Wt_low {j : ℕ} {ξ : Rd d} (h : lpPsi j ξ ≠ 0) :
    (2 : ℝ) ^ (2 * ((j : ℝ) - 1)) ≤ Wt ξ := by
  rcases j with _ | j
  · calc (2 : ℝ) ^ (2 * (((0 : ℕ) : ℝ) - 1)) ≤ 1 := by
          rw [show 2 * (((0 : ℕ) : ℝ) - 1) = -2 by norm_num]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      _ ≤ Wt ξ := one_le_Wt ξ
  · have hl := lpPsi_low h
    have e : (2 : ℝ) ^ (2 * (((j + 1 : ℕ) : ℝ) - 1)) = ((2 : ℝ) ^ j) ^ 2 := by
      rw [show 2 * (((j + 1 : ℕ) : ℝ) - 1) = ((2 * j : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, ← pow_mul, mul_comm]
    rw [e]
    unfold Wt
    nlinarith [pow_le_pow_left₀ (by positivity) hl.le 2]

/-- Auxiliary: on the support of `ψ_j`, `|2πξ|² ≤ 2^{2(j+1)}`. -/
theorem lpPsi_sq_high {j : ℕ} {ξ : Rd d} (h : lpPsi j ξ ≠ 0) :
    ‖(2 * π) • ξ‖ ^ 2 ≤ (2 : ℝ) ^ (2 * ((j : ℝ) + 1)) := by
  have e : (2 : ℝ) ^ (2 * ((j : ℝ) + 1)) = ((2 : ℝ) ^ (j + 1)) ^ 2 := by
    rw [show 2 * ((j : ℝ) + 1) = ((2 * (j + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, ← pow_mul, mul_comm]
  rw [e]
  exact pow_le_pow_left₀ (norm_nonneg _) (lpPsi_high h).le 2

/-! ### Band pieces of a real test -/

/-- Auxiliary: the complex band piece `𝓕⁻¹(ψ_j 𝓕φ)` of a real test (a Schwartz function). -/
def bandC {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) : 𝓢(Rd d, ℂ) :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (fun ξ => (lpPsi j ξ : ℂ)) (𝓕 (H1Mathlib.testSchwartz hφ)))

/-- **The band piece `f_j`** (`integrated_cameron_mean.tex` lines 63-65 at revision edf7085f
(book 1.1.3), smooth bands): the real part of `𝓕⁻¹(ψ_j 𝓕φ)`. -/
def band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) (x : Rd d) : ℝ := (bandC hφ j x).re

/-- Auxiliary: `|𝓕φ|²`, the Fourier density of a test. -/
def fsq {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (ξ : Rd d) : ℝ :=
  ‖𝓕 (H1Mathlib.testSchwartz hφ) ξ‖ ^ 2

/-- Auxiliary: `A_j = ‖ψ_j 𝓕φ‖₂²`. -/
def bandA {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) : ℝ :=
  ∫ ξ, lpPsi j ξ ^ 2 * fsq hφ ξ

/-- Auxiliary: `B_j = ‖ψ_j ⟨2πξ⟩^s 𝓕φ‖₂²`. -/
def bandB (s : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) : ℝ :=
  ∫ ξ, lpPsi j ξ ^ 2 * (Wt ξ ^ s * fsq hφ ξ)

/-- Auxiliary: `𝓕 f_j^ℂ = ψ_j 𝓕φ`. -/
theorem fourier_bandC {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) (ξ : Rd d) :
    𝓕 (bandC hφ j) ξ = (lpPsi j ξ : ℂ) * 𝓕 (H1Mathlib.testSchwartz hφ) ξ := by
  rw [bandC, fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply (lpPsiC_growth j),
    smul_eq_mul]

/-- Auxiliary: `|𝓕φ|²` is integrable. -/
theorem integrable_fsq {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    Integrable (fsq hφ) (volume : Measure (Rd d)) :=
  integrable_norm_sq_schwartz _

/-- Auxiliary: `|𝓕φ|²` is continuous. -/
theorem continuous_fsq {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : Continuous (fsq hφ) :=
  (𝓕 (H1Mathlib.testSchwartz hφ)).continuous.norm.pow 2

/-- Auxiliary: `⟨2πξ⟩^{2s}|𝓕φ|²` is integrable. -/
theorem integrable_Wt_fsq (s : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    Integrable (fun ξ => Wt ξ ^ s * fsq hφ ξ) (volume : Measure (Rd d)) :=
  integrable_weighted s hφ

/-- Auxiliary: `‖φ‖²_{H^s} = ∫ ⟨2πξ⟩^{2s} |𝓕φ|²`. -/
theorem norm_coord_sq' (s : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ‖coord s φ‖ ^ 2 = ∫ ξ, Wt ξ ^ s * fsq hφ ξ :=
  norm_coord_sq s hφ

/-- Auxiliary: Plancherel for the complex band piece. -/
theorem integral_norm_sq_bandC {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    ∫ x, ‖bandC hφ j x‖ ^ 2 = bandA hφ j := by
  rw [← SchwartzMap.integral_norm_sq_fourier, bandA]
  congr 1; funext ξ
  rw [fourier_bandC, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; rfl

/-- Auxiliary: a band piece is smooth. -/
theorem band_contDiff {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    ContDiff ℝ ∞ (band hφ j) :=
  Complex.reCLM.contDiff.comp ((bandC hφ j).smooth ⊤)

/-- Auxiliary: a band piece is in `L²`. -/
theorem memLp_band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    MemLp (band hφ j) 2 (volume : Measure (Rd d)) :=
  ((bandC hφ j).memLp 2 volume).re

/-- Auxiliary: `‖f_j‖₂² ≤ ‖ψ_j 𝓕φ‖₂²`. -/
theorem integral_band_sq_le {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    ∫ x, band hφ j x ^ 2 ≤ bandA hφ j := by
  rw [← integral_norm_sq_bandC]
  refine integral_mono (memLp_band hφ j).integrable_sq (integrable_norm_sq_schwartz _)
    fun x => ?_
  have h := Complex.abs_re_le_norm (bandC hφ j x)
  have h0 := abs_nonneg (bandC hφ j x).re
  simp only [band]
  nlinarith [sq_abs (bandC hφ j x).re]

/-- Auxiliary: the derivative of a band piece is the real part of the complex one. -/
theorem fderiv_band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) (x v : Rd d) :
    fderiv ℝ (band hφ j) x v = ((∂_{v} (bandC hφ j)) x).re := by
  have hd : DifferentiableAt ℝ (bandC hφ j) x :=
    ((bandC hφ j).smooth ⊤).differentiable (by simp) x
  have h := (Complex.reCLM.hasFDerivAt (x := bandC hφ j x)).comp x hd.hasFDerivAt
  rw [show band hφ j = Complex.reCLM ∘ (bandC hφ j) from rfl, h.fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

/-- Auxiliary: `|∇f_j|² ≤ Σ_k |∂_k f_j^ℂ|²`. -/
theorem norm_grad_band_sq_le {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) (x : Rd d) :
    ‖grad (band hφ j) x‖ ^ 2 ≤
      ∑ k : Fin d, ‖(∂_{H1Mathlib.eb d k} (bandC hφ j)) x‖ ^ 2 := by
  rw [← H1Mathlib.sum_sq_coord]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [grad, InnerProductSpace.toDual_symm_apply, fderiv_band]
  have h := Complex.abs_re_le_norm ((∂_{H1Mathlib.eb d k} (bandC hφ j)) x)
  have h0 := abs_nonneg ((∂_{H1Mathlib.eb d k} (bandC hφ j)) x).re
  nlinarith [sq_abs ((∂_{H1Mathlib.eb d k} (bandC hφ j)) x).re]

/-- Auxiliary: integrability of `Σ_k |∂_k f_j^ℂ|²`. -/
theorem integrable_sum_lineDeriv {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    Integrable (fun x => ∑ k : Fin d, ‖(∂_{H1Mathlib.eb d k} (bandC hφ j)) x‖ ^ 2)
      (volume : Measure (Rd d)) :=
  integrable_finsetSum _ fun _ _ => integrable_norm_sq_schwartz _

/-- Auxiliary: the gradient of a band piece is continuous. -/
theorem continuous_grad_band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    Continuous (grad (band hφ j)) :=
  (InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp
    ((band_contDiff hφ j).continuous_fderiv (by simp))

/-- Auxiliary: the gradient of a band piece is in `L²`. -/
theorem memLp_grad_band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    MemLp (grad (band hφ j)) 2 (volume : Measure (Rd d)) := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_grad_band hφ j).aestronglyMeasurable]
  refine (integrable_sum_lineDeriv hφ j).mono'
    ((continuous_grad_band hφ j).norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_grad_band_sq_le hφ j x

/-- Auxiliary: `ψ_j² g` is integrable for integrable `g`. -/
theorem integrable_psi_sq_mul (j : ℕ) {g : Rd d → ℝ}
    (hg : Integrable g (volume : Measure (Rd d))) :
    Integrable (fun ξ => lpPsi j ξ ^ 2 * g ξ) (volume : Measure (Rd d)) := by
  refine hg.bdd_mul (c := 1) ((lpPsi_contDiff j).continuous.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [lpPsi_nonneg j ξ, lpPsi_le_one j ξ]

/-- Auxiliary: the frequency bound `|2πξ|² ≤ 2^{2(j+1)}` on the band, integrated. -/
theorem integral_freq_le {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    ∫ ξ, ‖(2 * π) • ξ‖ ^ 2 * (lpPsi j ξ ^ 2 * fsq hφ ξ) ≤
      ∫ ξ, (2 : ℝ) ^ (2 * ((j : ℝ) + 1)) * (lpPsi j ξ ^ 2 * fsq hφ ξ) := by
  have hnn : ∀ ξ, 0 ≤ lpPsi j ξ ^ 2 * fsq hφ ξ := fun ξ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => mul_nonneg (sq_nonneg _) (hnn ξ))
    ((integrable_psi_sq_mul j (integrable_fsq hφ)).const_mul _)
    (Eventually.of_forall fun ξ => ?_)
  by_cases h0 : lpPsi j ξ = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (lpPsi_sq_high h0) (hnn ξ)

/-- Auxiliary: `Σ_k |𝓕 ∂_k F|² = |2πξ|² |𝓕F|²`. -/
theorem sum_norm_fourier_lineDeriv_sq (F : 𝓢(Rd d, ℂ)) (ξ : Rd d) :
    ∑ k : Fin d, ‖𝓕 (∂_{H1Mathlib.eb d k} F) ξ‖ ^ 2 = ‖(2 * π) • ξ‖ ^ 2 * ‖𝓕 F ξ‖ ^ 2 := by
  simp_rw [norm_fourier_lineDeriv_sq]
  rw [← Finset.sum_mul, ← Finset.mul_sum, H1Mathlib.sum_sq_coord, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  ring

/-- Auxiliary: Plancherel for the derivatives of the complex band piece. -/
theorem integral_sum_lineDeriv_eq {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    ∫ x, ∑ k : Fin d, ‖(∂_{H1Mathlib.eb d k} (bandC hφ j)) x‖ ^ 2 =
      ∫ ξ, ‖(2 * π) • ξ‖ ^ 2 * (lpPsi j ξ ^ 2 * fsq hφ ξ) := by
  have e : ∀ k : Fin d, ∫ x, ‖(∂_{H1Mathlib.eb d k} (bandC hφ j)) x‖ ^ 2 =
      ∫ ξ, ‖𝓕 (∂_{H1Mathlib.eb d k} (bandC hφ j)) ξ‖ ^ 2 := fun k =>
    (SchwartzMap.integral_norm_sq_fourier _).symm
  rw [integral_finsetSum _ fun _ _ => integrable_norm_sq_schwartz _, Finset.sum_congr rfl
    fun k _ => e k, ← integral_finsetSum _ fun _ _ => integrable_norm_sq_schwartz _]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [sum_norm_fourier_lineDeriv_sq, fourier_bandC, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  rfl

/-- Auxiliary: `‖∇f_j‖₂² ≤ 2^{2(j+1)} ‖ψ_j 𝓕φ‖₂²`. -/
theorem integral_grad_band_sq_le {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    ∫ x, ‖grad (band hφ j) x‖ ^ 2 ≤ (2 : ℝ) ^ (2 * ((j : ℝ) + 1)) * bandA hφ j := by
  have h1 := integral_mono ((memLp_two_iff_integrable_sq_norm
    (memLp_grad_band hφ j).aestronglyMeasurable).mp (memLp_grad_band hφ j))
    (integrable_sum_lineDeriv hφ j) (norm_grad_band_sq_le hφ j)
  have h2 := integral_sum_lineDeriv_eq hφ j
  have h3 := integral_freq_le hφ j
  have h4 : ∫ ξ, (2 : ℝ) ^ (2 * ((j : ℝ) + 1)) * (lpPsi j ξ ^ 2 * fsq hφ ξ) =
      (2 : ℝ) ^ (2 * ((j : ℝ) + 1)) * bandA hφ j := by
    rw [integral_const_mul]; rfl
  linarith

/-- Auxiliary: the classical gradient of a band piece is a weak gradient (integration by parts
against a test; the band piece is smooth). -/
theorem hasWeakGradient_band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    HasWeakGradient (band hφ j) (grad (band hφ j)) := by
  intro ψ hψ v
  have hf1 : ContDiff ℝ 1 (band hφ j) := (band_contDiff hφ j).of_le (by exact_mod_cast le_top)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := band hφ j) (g := ψ) (v := v)
    ((hf1.continuous_fderiv one_ne_zero).clm_apply continuous_const |>.mul hψ1.continuous
      |>.integrable_of_hasCompactSupport hψ.2.mul_left)
    ((hf1.continuous).mul ((hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport (hψ.2.fderiv_apply ℝ v).mul_left)
    ((hf1.continuous.mul hψ1.continuous).integrable_of_hasCompactSupport hψ.2.mul_left)
    (fun x _ => hf1.differentiable one_ne_zero x) (fun x _ => hψ1.differentiable one_ne_zero x)
  rw [key]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [grad, InnerProductSpace.toDual_symm_apply]

/-- Auxiliary: a band piece with its gradient is an `H¹` pair. -/
theorem isH1Pair_band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    IsH1Pair (band hφ j) (grad (band hφ j)) :=
  ⟨memLp_band hφ j, memLp_grad_band hφ j, hasWeakGradient_band hφ j⟩

/-- Auxiliary: `A_j ≥ 0`. -/
theorem bandA_nonneg {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) : 0 ≤ bandA hφ j :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Auxiliary: `B_j ≥ 0`. -/
theorem bandB_nonneg (s : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    0 ≤ bandB s hφ j :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (Wt_pos _).le _) (sq_nonneg _))

/-- Auxiliary: `(x^a y^b)² = (x²)^a (y²)^b` for `x, y ≥ 0`. -/
theorem sq_rpow_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (a b : ℝ) :
    (x ^ a * y ^ b) ^ 2 = (x ^ 2) ^ a * (y ^ 2) ^ b := by
  have e : ∀ z : ℝ, 0 ≤ z → ∀ c : ℝ, (z ^ c) ^ 2 = (z ^ 2) ^ c := fun z hz c => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz, ← Real.rpow_natCast z 2, ← Real.rpow_mul hz,
      mul_comm]
  rw [mul_pow, e x hx, e y hy]

/-- **The band bound** `N(f_j)² ≤ 2^{(j+1)α/2} ‖ψ_j 𝓕f‖₂²` (`E:cameron-dyadic-product`, first
inequality, `integrated_cameron_mean.tex` lines 66-73 at revision edf7085f (book
1.1.3), with the smooth band: the gradient symbol is at most `2^{j+1}` on the band). -/
theorem Nnorm_band_sq_le {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha4 : alpha ≤ 4) {φ : Rd d → ℝ}
    (hφ : IsTestFunction φ) (j : ℕ) :
    Nnorm alpha (band hφ j) (grad (band hφ j)) ^ 2 ≤
      (2 : ℝ) ^ (((j : ℝ) + 1) * alpha / 2) * bandA hφ j := by
  have hA := bandA_nonneg hφ j
  have h1 : l2 (band hφ j) ^ 2 ≤ bandA hφ j := by
    rw [SpatialFourLinear.l2_sq (memLp_band hφ j)]
    simpa [Real.norm_eq_abs, sq_abs] using integral_band_sq_le hφ j
  have h2 : l2 (grad (band hφ j)) ^ 2 ≤ (2 : ℝ) ^ (2 * ((j : ℝ) + 1)) * bandA hφ j := by
    rw [SpatialFourLinear.l2_sq (memLp_grad_band hφ j)]
    exact integral_grad_band_sq_le hφ j
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * ((j : ℝ) + 1)) := by positivity
  rw [SpatialFourLinear.Nnorm, sq_rpow_mul (SpatialFourLinear.l2_nonneg _)
    (SpatialFourLinear.l2_nonneg _)]
  calc (l2 (band hφ j) ^ 2) ^ (1 - alpha / 4) * (l2 (grad (band hφ j)) ^ 2) ^ (alpha / 4)
      ≤ bandA hφ j ^ (1 - alpha / 4) *
          ((2 : ℝ) ^ (2 * ((j : ℝ) + 1)) * bandA hφ j) ^ (alpha / 4) := by
        gcongr
        all_goals linarith
    _ = (2 : ℝ) ^ (((j : ℝ) + 1) * alpha / 2) * bandA hφ j := by
        rw [Real.mul_rpow hc hA, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have e : bandA hφ j ^ (1 - alpha / 4) * bandA hφ j ^ (alpha / 4) = bandA hφ j := by
          rw [← Real.rpow_add' hA (by norm_num), show 1 - alpha / 4 + alpha / 4 = 1 by ring,
            Real.rpow_one]
        rw [show 2 * ((j : ℝ) + 1) * (alpha / 4) = ((j : ℝ) + 1) * alpha / 2 by ring]
        linear_combination (2 : ℝ) ^ (((j : ℝ) + 1) * alpha / 2) * e

/-- **The weight on a band**: `‖ψ_j 𝓕f‖₂² ≤ 2^{2(1-j)s} ‖ψ_j ⟨2πξ⟩^s 𝓕f‖₂²` for `s ≥ 0`
(frequency support, `integrated_cameron_mean.tex` lines 69-73 at revision edf7085f (book
1.1.3)). -/
theorem bandA_le {s : ℝ} (hs : 0 ≤ s) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    bandA hφ j ≤ (2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s) * bandB s hφ j := by
  rw [bandA, bandB, ← integral_const_mul]
  refine integral_mono (integrable_psi_sq_mul j (integrable_fsq hφ))
    ((integrable_psi_sq_mul j (integrable_Wt_fsq s hφ)).const_mul _) fun ξ => ?_
  by_cases h0 : lpPsi j ξ = 0
  · simp [h0]
  · have hW := lpPsi_Wt_low h0
    have hWs : (2 : ℝ) ^ (2 * ((j : ℝ) - 1) * s) ≤ Wt ξ ^ s := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.rpow_le_rpow (by positivity) hW hs
    have hone : 1 ≤ (2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s) * Wt ξ ^ s := by
      have e : (2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s) * (2 : ℝ) ^ (2 * ((j : ℝ) - 1) * s) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [show 2 * (1 - (j : ℝ)) * s + 2 * ((j : ℝ) - 1) * s = 0 by ring, Real.rpow_zero]
      have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hWs hp]
    have hnn : 0 ≤ lpPsi j ξ ^ 2 * fsq hφ ξ := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc lpPsi j ξ ^ 2 * fsq hφ ξ ≤ ((2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s) * Wt ξ ^ s) *
          (lpPsi j ξ ^ 2 * fsq hφ ξ) := le_mul_of_one_le_left hnn hone
      _ = _ := by ring

/-- **The `H^s` square sum**: `Σ_{j<J} ‖ψ_j ⟨2πξ⟩^s 𝓕f‖₂² ≤ ‖f‖²_{H^s}` (`0 ≤ ψ_j ≤ 1`,
`Σ ψ_j ≤ 1`; the smooth-partition analogue of the sharp-band bound
`Σ_j 2^{2js}‖f_j‖₂² ≤ 2^{2s}‖f‖²_{H^s}` (`integrated_cameron_mean.tex` lines 76-77;
the bands `D_j` of lines 64-65), at revision edf7085f (book 1.1.3)). -/
theorem sum_bandB_le (s : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (J : ℕ) :
    ∑ j ∈ Finset.range J, bandB s hφ j ≤ ‖coord s φ‖ ^ 2 := by
  have hi : ∀ j ∈ Finset.range J, Integrable
      (fun ξ => lpPsi j ξ ^ 2 * (Wt ξ ^ s * fsq hφ ξ)) (volume : Measure (Rd d)) :=
    fun j _ => integrable_psi_sq_mul j (integrable_Wt_fsq s hφ)
  rw [norm_coord_sq' s hφ]
  unfold bandB
  rw [← integral_finsetSum _ hi]
  refine integral_mono (integrable_finsetSum _ hi) (integrable_Wt_fsq s hφ) fun ξ => ?_
  have hw : 0 ≤ Wt ξ ^ s * fsq hφ ξ := mul_nonneg (Real.rpow_nonneg (Wt_pos _).le _) (sq_nonneg _)
  simp only
  rw [← Finset.sum_mul]
  have h1 : ∑ j ∈ Finset.range J, lpPsi j ξ ^ 2 ≤ 1 :=
    (Finset.sum_le_sum fun j _ => by nlinarith [lpPsi_nonneg j ξ, lpPsi_le_one j ξ]).trans
      (sum_range_lpPsi_le_one J ξ)
  nlinarith

/-- **The constant `C_s`** of `L:cameron-fractional-products` (`integrated_cameron_mean.tex`
line 70 at revision edf7085f (book 1.1.3), with the smooth bands):
`C_s² = 2^{α/2+2s} / (1 - 2^{α/2-2s}) = Σ_j 2^{(j+1)α/2 + 2(1-j)s}`.  It depends on `α` and
`s` only. -/
def Cs (alpha s : ℝ) : ℝ := √((2 : ℝ) ^ (alpha / 2 + 2 * s) / (1 - (2 : ℝ) ^ (alpha / 2 - 2 * s)))

/-- Auxiliary: `C_s ≥ 0`. -/
theorem Cs_nonneg (alpha s : ℝ) : 0 ≤ Cs alpha s := Real.sqrt_nonneg _

/-- Auxiliary: the geometric bound `Σ_{j<J} 2^{(j+1)α/2} 2^{2(1-j)s} ≤ C_s²` for `α/4 < s`. -/
theorem sum_weights_le {alpha s : ℝ} (hs : alpha / 4 < s) (J : ℕ) :
    ∑ j ∈ Finset.range J, (2 : ℝ) ^ (((j : ℝ) + 1) * alpha / 2) * (2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s)
      ≤ Cs alpha s ^ 2 := by
  set r : ℝ := (2 : ℝ) ^ (alpha / 2 - 2 * s) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hK : (0 : ℝ) ≤ (2 : ℝ) ^ (alpha / 2 + 2 * s) := by positivity
  have e : ∀ j : ℕ, (2 : ℝ) ^ (((j : ℝ) + 1) * alpha / 2) * (2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s) =
      (2 : ℝ) ^ (alpha / 2 + 2 * s) * r ^ j := fun j => by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  simp_rw [e]
  rw [← Finset.mul_sum, Cs, ← hr, Real.sq_sqrt (div_nonneg hK (by linarith))]
  have hsum : ∑ i ∈ Finset.range J, r ^ i ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ (by linarith), mul_comm, mul_neg_geom_sum]
    linarith [pow_nonneg hr0 J]
  calc (2 : ℝ) ^ (alpha / 2 + 2 * s) * ∑ i ∈ Finset.range J, r ^ i
      ≤ (2 : ℝ) ^ (alpha / 2 + 2 * s) * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hsum hK
    _ = _ := by ring

/-- **`E:cameron-dyadic-product`, second inequality** (`integrated_cameron_mean.tex` lines
66-73 at revision edf7085f (book 1.1.3)): `Σ_{j<J} N(f_j) ≤ C_s ‖f‖_{H^s}` for a real
test `f`, `0 ≤ α ≤ 4`, `α/4 < s`. -/
theorem sum_Nnorm_band_le {alpha s : ℝ} (ha0 : 0 ≤ alpha) (ha4 : alpha ≤ 4) (hs : alpha / 4 < s)
    {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (J : ℕ) :
    ∑ j ∈ Finset.range J, Nnorm alpha (band hφ j) (grad (band hφ j)) ≤
      Cs alpha s * ‖coord s φ‖ := by
  have hs0 : 0 ≤ s := by linarith
  set w : ℕ → ℝ := fun j =>
    (2 : ℝ) ^ (((j : ℝ) + 1) * alpha / 2) * (2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s) with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => by positivity
  have hN : ∀ j, Nnorm alpha (band hφ j) (grad (band hφ j)) ≤
      √(w j) * √(bandB s hφ j) := fun j => by
    rw [← Real.sqrt_mul (hw0 j)]
    refine Real.le_sqrt_of_sq_le ?_
    calc Nnorm alpha (band hφ j) (grad (band hφ j)) ^ 2
        ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * alpha / 2) * bandA hφ j := Nnorm_band_sq_le ha0 ha4 hφ j
      _ ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * alpha / 2) *
            ((2 : ℝ) ^ (2 * (1 - (j : ℝ)) * s) * bandB s hφ j) :=
          mul_le_mul_of_nonneg_left (bandA_le hs0 hφ j) (by positivity)
      _ = w j * bandB s hφ j := by rw [hw]; ring
  calc ∑ j ∈ Finset.range J, Nnorm alpha (band hφ j) (grad (band hφ j))
      ≤ ∑ j ∈ Finset.range J, √(w j) * √(bandB s hφ j) := Finset.sum_le_sum fun j _ => hN j
    _ ≤ √(∑ j ∈ Finset.range J, √(w j) ^ 2) * √(∑ j ∈ Finset.range J, √(bandB s hφ j) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Cs alpha s * ‖coord s φ‖ := by
        simp_rw [Real.sq_sqrt (hw0 _), Real.sq_sqrt (bandB_nonneg s hφ _)]
        refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Cs_nonneg _ _)
        · rw [← Real.sqrt_sq (Cs_nonneg alpha s)]
          exact Real.sqrt_le_sqrt (sum_weights_le hs J)
        · rw [← Real.sqrt_sq (norm_nonneg (coord s φ))]
          exact Real.sqrt_le_sqrt (sum_bandB_le s hφ J)

/-! ### The band series of a test converges pointwise -/

/-- Auxiliary: the complex band piece as a Fourier integral. -/
theorem bandC_apply {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) (x : Rd d) :
    bandC hφ j x = ∫ ξ, 𝐞 ⟪ξ, x⟫ • ((lpPsi j ξ : ℂ) * 𝓕 (H1Mathlib.testSchwartz hφ) ξ) := by
  rw [bandC, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [SchwartzMap.smulLeftCLM_apply_apply (lpPsiC_growth j), smul_eq_mul]

/-- Auxiliary: integrability of `e^{2πi⟪ξ,x⟫} g(ξ) 𝓕φ(ξ)` for `|g| ≤ 1`. -/
theorem integrable_phase_mul {g : Rd d → ℝ} (hg : Continuous g) (hg1 : ∀ ξ, |g ξ| ≤ 1)
    {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (x : Rd d) :
    Integrable (fun ξ => 𝐞 ⟪ξ, x⟫ • ((g ξ : ℂ) * 𝓕 (H1Mathlib.testSchwartz hφ) ξ))
      (volume : Measure (Rd d)) := by
  have hF := (𝓕 (H1Mathlib.testSchwartz hφ))
  refine (𝓕 (H1Mathlib.testSchwartz hφ)).integrable.norm.mono' ?_
    (Eventually.of_forall fun ξ => ?_)
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      ((Complex.continuous_ofReal.comp hg).mul
        (𝓕 (H1Mathlib.testSchwartz hφ)).continuous)).aestronglyMeasurable
  · rw [Circle.norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hg1 ξ)

/-- Auxiliary: the partial band sums are `𝓕⁻¹(S_J 𝓕φ)`. -/
theorem sum_bandC_apply {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (J : ℕ) (x : Rd d) :
    ∑ j ∈ Finset.range (J + 1), bandC hφ j x =
      ∫ ξ, 𝐞 ⟪ξ, x⟫ • ((lpS J ξ : ℂ) * 𝓕 (H1Mathlib.testSchwartz hφ) ξ) := by
  simp_rw [bandC_apply]
  rw [← integral_finsetSum _ fun j _ => integrable_phase_mul (lpPsi_contDiff j).continuous
    (fun ξ => by rw [abs_of_nonneg (lpPsi_nonneg j ξ)]; exact lpPsi_le_one j ξ) hφ x]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [← Finset.smul_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, sum_range_lpPsi]

/-- Auxiliary: the complex band series converges pointwise (dominated convergence). -/
theorem tendsto_sum_bandC {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (x : Rd d) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), bandC hφ j x) atTop (𝓝 (φ x : ℂ)) := by
  simp_rw [sum_bandC_apply]
  set hS : 𝓢(Rd d, ℂ) := H1Mathlib.testSchwartz hφ
  have h0 : 𝓕⁻ (𝓕 hS : 𝓢(Rd d, ℂ)) = hS := fourierInv_fourier_eq hS
  have hinv : (𝓕⁻ (𝓕 hS : 𝓢(Rd d, ℂ)) : 𝓢(Rd d, ℂ)) x = hS x := by rw [h0]
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq] at hinv
  have hx : (φ x : ℂ) = ∫ ξ, 𝐞 ⟪ξ, x⟫ • ((1 : ℂ) * 𝓕 hS ξ) := by
    rw [show (φ x : ℂ) = hS x from rfl, ← hinv]; simp only [one_mul]; rfl
  rw [hx]
  refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕 hS ξ‖) (fun J => ?_)
    (𝓕 hS).integrable.norm (fun J => Eventually.of_forall fun ξ => ?_)
    (Eventually.of_forall fun ξ => ?_)
  · exact (integrable_phase_mul (lpS_contDiff J).continuous (fun ξ => by
      rw [abs_of_nonneg (lpS_nonneg J ξ)]; exact lpS_le_one J ξ) hφ x).aestronglyMeasurable
  · rw [Circle.norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (lpS_nonneg J ξ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (lpS_le_one J ξ)
  · have t : Tendsto (fun J => (lpS J ξ : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (tendsto_lpS ξ)
    rw [Complex.ofReal_one] at t
    exact (t.mul_const _).const_smul _

/-- **The band series of a real test** (`integrated_cameron_mean.tex` lines 78-80 at revision
edf7085f (book 1.1.3), for tests and smooth bands): `Σ_{j ≤ J} f_j(x) → f(x)` for
every `x`. -/
theorem tendsto_sum_band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (x : Rd d) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), band hφ j x) atTop (𝓝 (φ x)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sum_bandC hφ x)
  simp only [Complex.ofReal_re] at h
  refine h.congr fun J => ?_
  simp only [Function.comp, Complex.re_sum, band]

/-- Auxiliary: `|φ(x)| ≤ Σ_j |f_j(x)|`. -/
theorem enorm_le_tsum_band {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (x : Rd d) :
    ‖φ x‖ₑ ≤ ∑' j, ‖band hφ j x‖ₑ :=
  le_of_tendsto' ((continuous_enorm.tendsto _).comp (tendsto_sum_band hφ x)) fun _ =>
    (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)

/-- Auxiliary: `Σ_j N(f_j) ≤ C_s ‖φ‖_{H^s}` in `ℝ≥0∞`. -/
theorem tsum_Nnorm_band_le {alpha s : ℝ} (ha0 : 0 ≤ alpha) (ha4 : alpha ≤ 4)
    (hs : alpha / 4 < s) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ∑' j, ENNReal.ofReal (Nnorm alpha (band hφ j) (grad (band hφ j))) ≤
      ENNReal.ofReal (Cs alpha s * ‖coord s φ‖) := by
  refine ENNReal.tsum_le_of_sum_range_le fun J => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => SpatialFourLinear.Nnorm_nonneg _ _ _]
  exact ENNReal.ofReal_le_ofReal (sum_Nnorm_band_le ha0 ha4 hs hφ J)

/-! ### Four-fold series in `ℝ≥0∞` -/

/-- Auxiliary: a product of four series in `ℝ≥0∞` is the four-fold series. -/
theorem prod_tsum4 (x₁ x₂ x₃ x₄ : ℕ → ℝ≥0∞) :
    (∑' a, x₁ a) * (∑' b, x₂ b) * (∑' c, x₃ c) * (∑' e, x₄ e) =
      ∑' a, ∑' b, ∑' c, ∑' e, x₁ a * x₂ b * x₃ c * x₄ e := by
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-- Auxiliary: Tonelli for a four-fold product of series. -/
theorem lintegral_le_tsum4 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (c₁ c₂ c₃ c₄ : ℕ → α → ℝ≥0∞) (h₁ : ∀ j, Measurable (c₁ j)) (h₂ : ∀ j, Measurable (c₂ j))
    (h₃ : ∀ j, Measurable (c₃ j)) (h₄ : ∀ j, Measurable (c₄ j)) {F : α → ℝ≥0∞}
    (hF : ∀ p, F p ≤ (∑' j, c₁ j p) * (∑' j, c₂ j p) * (∑' j, c₃ j p) * (∑' j, c₄ j p)) :
    ∫⁻ p, F p ∂μ ≤ ∑' a, ∑' b, ∑' c, ∑' e, ∫⁻ p, c₁ a p * c₂ b p * c₃ c p * c₄ e p ∂μ := by
  calc ∫⁻ p, F p ∂μ
      ≤ ∫⁻ p, ∑' a, ∑' b, ∑' c, ∑' e, c₁ a p * c₂ b p * c₃ c p * c₄ e p ∂μ :=
        lintegral_mono fun p => (hF p).trans_eq (prod_tsum4 _ _ _ _)
    _ = _ := by
        rw [lintegral_tsum fun a => ?_]
        · refine tsum_congr fun a => ?_
          rw [lintegral_tsum fun b => ?_]
          · refine tsum_congr fun b => ?_
            rw [lintegral_tsum fun c => ?_]
            · refine tsum_congr fun c => ?_
              rw [lintegral_tsum fun e => ?_]
              exact (((h₁ a).mul (h₂ b)).mul (h₃ c)).mul (h₄ e) |>.aemeasurable
            · exact (Measurable.tsum fun e =>
                (((h₁ a).mul (h₂ b)).mul (h₃ c)).mul (h₄ e)).aemeasurable
          · exact (Measurable.tsum fun c => Measurable.tsum fun e =>
              (((h₁ a).mul (h₂ b)).mul (h₃ c)).mul (h₄ e)).aemeasurable
        · exact (Measurable.tsum fun b => Measurable.tsum fun c =>
            Measurable.tsum fun e =>
              (((h₁ a).mul (h₂ b)).mul (h₃ c)).mul (h₄ e)).aemeasurable

/-! ### `E:cameron-fractional-absolute` for real tests -/

/-- Auxiliary: `N(f_j)` in `ℝ≥0∞`. -/
def bandN (alpha : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Nnorm alpha (band hφ j) (grad (band hφ j)))

/-- Auxiliary: measurability of `p ↦ ‖f_j(p.1)‖ₑ` and `p ↦ ‖f_j(p.1 - p.2)‖ₑ`. -/
theorem measurable_band_fst {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    Measurable fun p : Rd d × Rd d => ‖band hφ j p.1‖ₑ :=
  (continuous_enorm.comp ((band_contDiff hφ j).continuous.comp continuous_fst)).measurable

/-- Auxiliary: measurability of `p ↦ ‖f_j(p.1 - p.2)‖ₑ`. -/
theorem measurable_band_sub {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (j : ℕ) :
    Measurable fun p : Rd d × Rd d => ‖band hφ j (p.1 - p.2)‖ₑ :=
  (continuous_enorm.comp ((band_contDiff hφ j).continuous.comp
    (continuous_fst.sub continuous_snd))).measurable

/-- **`E:cameron-fractional-absolute` for real tests** (`integrated_cameron_mean.tex` lines
37-41, proof Step 3 lines 80-86, at revision edf7085f (book 1.1.3)): under the
absolute four-linear bound of `P:spatial-four-linear` with constant `R` (`SquareBound`), for
`0 ≤ α ≤ 4` and `α/4 < s`,
`∫ |f₁(x) f₂(x) f₃(x-y) f₄(x-y)| dx Γ(dy) ≤ C_s⁴ R ∏ ‖f_j‖_{H^s}` (band series and Tonelli). -/
theorem test_absolute {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R s : ℝ}
    (ha0 : 0 ≤ alpha) (ha4 : alpha ≤ 4) (hs : alpha / 4 < s) (hB : SquareBound Γ alpha R)
    (hR : 0 ≤ R) {φ₁ φ₂ φ₃ φ₄ : Rd d → ℝ} (h₁ : IsTestFunction φ₁) (h₂ : IsTestFunction φ₂)
    (h₃ : IsTestFunction φ₃) (h₄ : IsTestFunction φ₄) :
    ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
      ENNReal.ofReal (Cs alpha s ^ 4 * R *
        (‖coord s φ₁‖ * ‖coord s φ₂‖ * ‖coord s φ₃‖ * ‖coord s φ₄‖)) := by
  have step1 := lintegral_le_tsum4 (μ := pairMeasure Γ)
    (fun j p => ‖band h₁ j p.1‖ₑ) (fun j p => ‖band h₂ j p.1‖ₑ)
    (fun j p => ‖band h₃ j (p.1 - p.2)‖ₑ) (fun j p => ‖band h₄ j (p.1 - p.2)‖ₑ)
    (measurable_band_fst h₁) (measurable_band_fst h₂) (measurable_band_sub h₃)
    (measurable_band_sub h₄)
    (F := fun p => ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ) (fun p => by
      simp only [enorm_mul]
      gcongr
      · exact enorm_le_tsum_band h₁ _
      · exact enorm_le_tsum_band h₂ _
      · exact enorm_le_tsum_band h₃ _
      · exact enorm_le_tsum_band h₄ _)
  have hterm : ∀ a b c e, ∫⁻ p, ‖band h₁ a p.1‖ₑ * ‖band h₂ b p.1‖ₑ *
      ‖band h₃ c (p.1 - p.2)‖ₑ * ‖band h₄ e (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
      ENNReal.ofReal R *
        (bandN alpha h₁ a * bandN alpha h₂ b * bandN alpha h₃ c * bandN alpha h₄ e) :=
      fun a b c e => by
    have h := SpatialFourLinear.four_lintegral_le hB hR (isH1Pair_band h₁ a)
      (isH1Pair_band h₂ b) (isH1Pair_band h₃ c) (isH1Pair_band h₄ e)
    simp only [enorm_mul] at h
    refine h.trans (le_of_eq ?_)
    have N1 := SpatialFourLinear.Nnorm_nonneg alpha (band h₁ a) (grad (band h₁ a))
    have N2 := SpatialFourLinear.Nnorm_nonneg alpha (band h₂ b) (grad (band h₂ b))
    have N3 := SpatialFourLinear.Nnorm_nonneg alpha (band h₃ c) (grad (band h₃ c))
    have N4 := SpatialFourLinear.Nnorm_nonneg alpha (band h₄ e) (grad (band h₄ e))
    simp only [bandN]
    rw [ENNReal.ofReal_mul hR, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul N1]
  have hC := Cs_nonneg alpha s
  calc ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ)
      ≤ ∑' a, ∑' b, ∑' c, ∑' e, ENNReal.ofReal R *
          (bandN alpha h₁ a * bandN alpha h₂ b * bandN alpha h₃ c * bandN alpha h₄ e) :=
        step1.trans (ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun b =>
          ENNReal.tsum_le_tsum fun c => ENNReal.tsum_le_tsum fun e => hterm a b c e)
    _ = ENNReal.ofReal R * ((∑' j, bandN alpha h₁ j) * (∑' j, bandN alpha h₂ j) *
          (∑' j, bandN alpha h₃ j) *
          (∑' j, bandN alpha h₄ j)) := by
        rw [prod_tsum4]; simp only [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal R * (ENNReal.ofReal (Cs alpha s * ‖coord s φ₁‖) *
          ENNReal.ofReal (Cs alpha s * ‖coord s φ₂‖) * ENNReal.ofReal (Cs alpha s * ‖coord s φ₃‖) *
          ENNReal.ofReal (Cs alpha s * ‖coord s φ₄‖)) := by
        gcongr
        · exact tsum_Nnorm_band_le ha0 ha4 hs h₁
        · exact tsum_Nnorm_band_le ha0 ha4 hs h₂
        · exact tsum_Nnorm_band_le ha0 ha4 hs h₃
        · exact tsum_Nnorm_band_le ha0 ha4 hs h₄
    _ = _ := by
        have c1 := mul_nonneg hC (norm_nonneg (coord s φ₁))
        have c2 := mul_nonneg hC (norm_nonneg (coord s φ₂))
        have c3 := mul_nonneg hC (norm_nonneg (coord s φ₃))
        rw [← ENNReal.ofReal_mul c1, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hR]
        congr 1; ring

/-! ### Physical representatives -/

/-- Auxiliary: the norm of a class of `H^s` is the `L²` norm of its coordinate. -/
theorem norm_Hsob (s : ℝ) (u : Hsob d s) :
    ‖u‖ = ‖((show HR d from u) : Lp ℂ 2 (volume : Measure (Rd d)))‖ := rfl

/-- Auxiliary: `‖[φ] - u‖_{H^s}` is the `L²` distance of the coordinates. -/
theorem norm_toHsob_sub (s : ℝ) (φ : Rd d → ℝ) (u : Hsob d s) :
    ‖toHsob s φ - u‖ = ‖coord s φ - ((show HR d from u) : Lp ℂ 2 (volume : Measure (Rd d)))‖ :=
  rfl

/-- Auxiliary: `|⟨2πξ⟩^{-s}| ≤ 1` for `s ≥ 0`. -/
theorem norm_msWeight_neg_le {s : ℝ} (hs : 0 ≤ s) (ξ : Rd d) : ‖msWeight (-s) ξ‖ ≤ 1 := by
  rw [UniformMeanCutoff.norm_msWeight]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_Wt ξ) (by linarith)

/-- **The physical function of a test** (`IsPhysRep` for `[φ]`): the coordinate of `[φ]` is
`⟨2πξ⟩^s 𝓕φ`. -/
theorem isPhysRep_test (s : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    IsPhysRep s (toHsob (d := d) s φ) φ := by
  refine ⟨(H1Mathlib.testSchwartz hφ).memLp 2 volume, ?_⟩
  have e : ((H1Mathlib.testSchwartz hφ).memLp 2 volume).toLp (fun x => (φ x : ℂ)) =
      (H1Mathlib.testSchwartz hφ).toLp 2 volume := rfl
  rw [e, SchwartzMap.toLp_fourier_eq]
  filter_upwards [coeFn_coord s hφ, (𝓕 (H1Mathlib.testSchwartz hφ)).coeFn_toLp 2
    (volume : Measure (Rd d))] with ξ h1 h2
  change (coord s φ : Rd d → ℂ) ξ = _
  rw [h1, h2]

/-- Auxiliary: the coordinate of a difference. -/
theorem coe_Hsob_sub {s : ℝ} (u v : Hsob d s) :
    ((show HR d from u - v) : Lp ℂ 2 (volume : Measure (Rd d))) =
      ((show HR d from u) : Lp ℂ 2 (volume : Measure (Rd d))) - (show HR d from v) := rfl

/-- Auxiliary: physical functions of differences. -/
theorem isPhysRep_sub {s : ℝ} {u v : Hsob d s} {f g : Rd d → ℝ} (hu : IsPhysRep s u f)
    (hv : IsPhysRep s v g) : IsPhysRep s (u - v) (fun x => f x - g x) := by
  obtain ⟨hf, hfu⟩ := hu
  obtain ⟨hg, hgv⟩ := hv
  have ef : (fun x => ((f x - g x : ℝ) : ℂ)) = (fun x => (f x : ℂ)) - (fun x => (g x : ℂ)) := by
    funext x; simp
  have hfg : MemLp (fun x => ((f x - g x : ℝ) : ℂ)) 2 (volume : Measure (Rd d)) := by
    rw [ef]; exact hf.sub hg
  refine ⟨hfg, ?_⟩
  have e : hfg.toLp _ = hf.toLp _ - hg.toLp _ := by
    rw [← MemLp.toLp_sub]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by simp)
  have hF : 𝓕 (hf.toLp _ - hg.toLp _) = 𝓕 (hf.toLp _) - 𝓕 (hg.toLp _) :=
    (Lp.fourierTransformₗᵢ (Rd d) ℂ).map_sub _ _
  rw [e, hF, coe_Hsob_sub]
  filter_upwards [Lp.coeFn_sub ((show HR d from u) : Lp ℂ 2 (volume : Measure (Rd d)))
      ((show HR d from v) : Lp ℂ 2 (volume : Measure (Rd d))),
    Lp.coeFn_sub (𝓕 (hf.toLp _) : Lp ℂ 2 (volume : Measure (Rd d))) (𝓕 (hg.toLp _)),
    hfu, hgv] with ξ h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h3, h4, h2, Pi.sub_apply, mul_sub]

/-- **The `L²` distance of physical functions is at most the `H^s` distance** (`s ≥ 0`;
Plancherel and `⟨2πξ⟩^{-s} ≤ 1`). -/
theorem eLpNorm_phys_le {s : ℝ} (hs : 0 ≤ s) {u : Hsob d s} {f : Rd d → ℝ} (hu : IsPhysRep s u f)
    {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    eLpNorm (fun x => φ x - f x) 2 volume ≤ ENNReal.ofReal ‖toHsob s φ - u‖ := by
  obtain ⟨hf, hfu⟩ := isPhysRep_sub (isPhysRep_test s hφ) hu
  set D := hf.toLp _
  have h1 : eLpNorm (fun x => φ x - f x) 2 volume = ENNReal.ofReal ‖D‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top D), eLpNorm_congr_ae hf.coeFn_toLp]
    have hm : AEStronglyMeasurable (fun x => φ x - f x) volume := by
      simpa using hf.aestronglyMeasurable.re
    exact eLpNorm_congr_norm_ae hm hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        exact (Complex.norm_real _).symm)
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Lp.norm_fourier_eq D]
  have hsq : ‖(𝓕 D : Lp ℂ 2 volume)‖ ^ 2 ≤ ‖toHsob s φ - u‖ ^ 2 := by
    rw [H1Mathlib.norm_sq_eq_integral, norm_Hsob, H1Mathlib.norm_sq_eq_integral]
    refine integral_mono_ae (H1Mathlib.integrable_norm_sq _) (H1Mathlib.integrable_norm_sq _) ?_
    filter_upwards [hfu] with ξ h
    rw [h, norm_mul]
    have hw : ‖msWeight s ξ‖ ≥ 1 := by
      rw [UniformMeanCutoff.norm_msWeight]
      exact Real.one_le_rpow (one_le_Wt ξ) (by linarith)
    have := norm_nonneg ((𝓕 D : Lp ℂ 2 volume) ξ)
    nlinarith [mul_le_mul_of_nonneg_right hw this]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Auxiliary: approximation of an element of `H^s` (`0 ≤ s ≤ 1`) with a physical function by
real tests, in `H^s` and (for the physical functions) in `L²`. -/
theorem exists_test_approx {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {u : Hsob d s} {f : Rd d → ℝ}
    (hu : IsPhysRep s u f) :
    ∃ φ : ℕ → Rd d → ℝ, (∀ n, IsTestFunction (φ n)) ∧
      Tendsto (fun n => toHsob s (φ n)) atTop (𝓝 u) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) := by
  have hex : ∀ n : ℕ, ∃ φ, IsTestFunction φ ∧ ‖toHsob s φ - u‖ < 1 / ((n : ℝ) + 1) :=
    fun n => exists_test_coord_near s hs1 (show HR d from u).2 (by positivity)
  choose φ hφ hφu using hex
  have hlim : Tendsto (fun n => ‖toHsob s (φ n) - u‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => (hφu n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨φ, hφ, tendsto_iff_norm_sub_tendsto_zero.mpr hlim, ?_⟩
  have h0 : Tendsto (fun n => ENNReal.ofReal ‖toHsob s (φ n) - u‖) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => zero_le)
    fun n => eLpNorm_phys_le hs0 hu (hφ n)

/-- Auxiliary: a further subsequence along which `L²` convergence becomes a.e. convergence. -/
theorem subseq_ae {F : ℕ → Rd d → ℝ} {f : Rd d → ℝ}
    (hl : Tendsto (fun n => eLpNorm (fun x => F n x - f x) 2 volume) atTop (𝓝 0)) {ns : ℕ → ℕ}
    (hns : StrictMono ns) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ x, Tendsto (fun i => F (ns (ms i)) x) atTop (𝓝 (f x)) :=
  (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (f := fun i => F (ns i)) (g := f) (by norm_num)
    (hl.comp hns.tendsto_atTop)).exists_seq_tendsto_ae

/-- **`E:cameron-fractional-absolute` for physical functions of arbitrary `H^s` elements**
(`integrated_cameron_mean.tex` lines 37-41 and 80-86 at revision edf7085f (book
1.1.3)), from the test case: test approximants converge in `H^s`, their physical functions
in `L²`, hence a.e. along a subsequence and `ν`-a.e. at both positions; Fatou. -/
theorem phys_absolute {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {s K : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1)
    (hT : ∀ φ₁ φ₂ φ₃ φ₄ : Rd d → ℝ, IsTestFunction φ₁ → IsTestFunction φ₂ → IsTestFunction φ₃ →
      IsTestFunction φ₄ →
      ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (K * (‖coord s φ₁‖ * ‖coord s φ₂‖ * ‖coord s φ₃‖ * ‖coord s φ₄‖)))
    {u₁ u₂ u₃ u₄ : Hsob d s} {f₁ f₂ f₃ f₄ : Rd d → ℝ} (h₁ : IsPhysRep s u₁ f₁)
    (h₂ : IsPhysRep s u₂ f₂) (h₃ : IsPhysRep s u₃ f₃) (h₄ : IsPhysRep s u₄ f₄) :
    ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
      ENNReal.ofReal (K * (‖u₁‖ * ‖u₂‖ * ‖u₃‖ * ‖u₄‖)) := by
  obtain ⟨φ₁, t₁, c₁, l₁⟩ := exists_test_approx hs0 hs1 h₁
  obtain ⟨φ₂, t₂, c₂, l₂⟩ := exists_test_approx hs0 hs1 h₂
  obtain ⟨φ₃, t₃, c₃, l₃⟩ := exists_test_approx hs0 hs1 h₃
  obtain ⟨φ₄, t₄, c₄, l₄⟩ := exists_test_approx hs0 hs1 h₄
  obtain ⟨m₁, hm₁, a₁⟩ := subseq_ae l₁ strictMono_id
  obtain ⟨m₂, hm₂, a₂⟩ := subseq_ae l₂ hm₁
  obtain ⟨m₃, hm₃, a₃⟩ := subseq_ae l₃ (hm₁.comp hm₂)
  obtain ⟨m₄, hm₄, a₄⟩ := subseq_ae l₄ ((hm₁.comp hm₂).comp hm₃)
  set N : ℕ → ℕ := fun i => m₁ (m₂ (m₃ (m₄ i))) with hN
  have hNm : StrictMono N := ((hm₁.comp hm₂).comp hm₃).comp hm₄
  have b₁ : ∀ᵐ x, Tendsto (fun i => φ₁ (N i) x) atTop (𝓝 (f₁ x)) := by
    filter_upwards [a₁] with x hx
    exact hx.comp ((hm₂.comp hm₃).comp hm₄).tendsto_atTop
  have b₂ : ∀ᵐ x, Tendsto (fun i => φ₂ (N i) x) atTop (𝓝 (f₂ x)) := by
    filter_upwards [a₂] with x hx
    exact hx.comp (hm₃.comp hm₄).tendsto_atTop
  have b₃ : ∀ᵐ x, Tendsto (fun i => φ₃ (N i) x) atTop (𝓝 (f₃ x)) := by
    filter_upwards [a₃] with x hx
    exact hx.comp hm₄.tendsto_atTop
  have b₄ : ∀ᵐ x, Tendsto (fun i => φ₄ (N i) x) atTop (𝓝 (f₄ x)) := a₄
  set F : ℕ → Rd d × Rd d → ℝ≥0∞ := fun i p =>
    ‖φ₁ (N i) p.1 * φ₂ (N i) p.1 * φ₃ (N i) (p.1 - p.2) * φ₄ (N i) (p.1 - p.2)‖ₑ with hF
  have hFm : ∀ i, AEMeasurable (F i) (pairMeasure Γ) := fun i => by
    have k₁ := (t₁ (N i)).1.continuous
    have k₂ := (t₂ (N i)).1.continuous
    have k₃ := (t₃ (N i)).1.continuous
    have k₄ := (t₄ (N i)).1.continuous
    exact (continuous_enorm.comp ((((k₁.comp continuous_fst).mul (k₂.comp continuous_fst)).mul
      (k₃.comp (continuous_fst.sub continuous_snd))).mul
      (k₄.comp (continuous_fst.sub continuous_snd)))).measurable.aemeasurable
  have hlim : ∀ᵐ p ∂(pairMeasure Γ), Tendsto (fun i => F i p) atTop
      (𝓝 ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ) := by
    filter_upwards [OccupationKernelRow.ae_pair_of_ae Γ b₁, OccupationKernelRow.ae_pair_of_ae Γ b₂,
      OccupationKernelRow.ae_pair_of_ae Γ b₃, OccupationKernelRow.ae_pair_of_ae Γ b₄]
      with p p₁ p₂ p₃ p₄
    exact (continuous_enorm.tendsto _).comp (((p₁.1.mul p₂.1).mul p₃.2).mul p₄.2)
  have hB : ∀ i, ∫⁻ p, F i p ∂(pairMeasure Γ) ≤ ENNReal.ofReal (K * (‖toHsob s (φ₁ (N i))‖ *
      ‖toHsob s (φ₂ (N i))‖ * ‖toHsob s (φ₃ (N i))‖ * ‖toHsob s (φ₄ (N i))‖)) := fun i =>
    hT _ _ _ _ (t₁ _) (t₂ _) (t₃ _) (t₄ _)
  have hBlim : Tendsto (fun i => ENNReal.ofReal (K * (‖toHsob s (φ₁ (N i))‖ *
      ‖toHsob s (φ₂ (N i))‖ * ‖toHsob s (φ₃ (N i))‖ * ‖toHsob s (φ₄ (N i))‖))) atTop
      (𝓝 (ENNReal.ofReal (K * (‖u₁‖ * ‖u₂‖ * ‖u₃‖ * ‖u₄‖)))) := by
    have n₁ := (c₁.comp hNm.tendsto_atTop).norm
    have n₂ := (c₂.comp hNm.tendsto_atTop).norm
    have n₃ := (c₃.comp hNm.tendsto_atTop).norm
    have n₄ := (c₄.comp hNm.tendsto_atTop).norm
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (((n₁.mul n₂).mul n₃).mul n₄))
  calc ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ)
      = ∫⁻ p, liminf (fun i => F i p) atTop ∂(pairMeasure Γ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlim] with p hp
        exact hp.liminf_eq.symm
    _ ≤ liminf (fun i => ∫⁻ p, F i p ∂(pairMeasure Γ)) atTop := lintegral_liminf_le' hFm
    _ ≤ liminf (fun i => ENNReal.ofReal (K * (‖toHsob s (φ₁ (N i))‖ *
          ‖toHsob s (φ₂ (N i))‖ * ‖toHsob s (φ₃ (N i))‖ * ‖toHsob s (φ₄ (N i))‖))) atTop :=
        liminf_le_liminf (Eventually.of_forall hB)
    _ = _ := hBlim.liminf_eq

/-! ### The product map -/

open UniformMeanCutoff (toHsobL) in
/-- **Density of real tests in `H^s`, `s ≤ 1`** (`integrated_cameron_mean.tex` lines 93-97 at
revision edf7085f (book 1.1.3): "Compact smooth functions are dense in `H^s`"). -/
theorem denseRange_toHsobL {s : ℝ} (hs1 : s ≤ 1) : DenseRange (toHsobL (d := d) s) := by
  refine Metric.denseRange_iff.mpr fun x r hr => ?_
  obtain ⟨φ, hφ, h⟩ := exists_test_coord_near s hs1 (show HR d from x).2 hr
  refine ⟨⟨φ, hφ⟩, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact h

/-- Auxiliary: `[φ + ψ]_{H_sp} = [φ]_{H_sp} + [ψ]_{H_sp}` on tests. -/
theorem toHsp_add (S : SpData d) {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ)
    (hψ : IsTestFunction ψ) : toHsp S (φ + ψ) = toHsp S φ + toHsp S ψ := by
  have hd : IsTestFunction (φ + ψ) := isTest_add hφ hψ
  rw [OccupationCompletion.toHsp_of_test hd, OccupationCompletion.toHsp_of_test hφ,
    OccupationCompletion.toHsp_of_test hψ, ← UniformSpace.Completion.coe_add]
  rfl

/-- Auxiliary: `g ↦ [f g]_{H_sp}` on the tests, for a fixed real test `f`. -/
def mulSpL (S : SpData d) {f : Rd d → ℝ} (hf : IsTestFunction f) : testSub d →ₗ[ℝ] Hsp S where
  toFun g := toHsp S fun x => f x * (g : Rd d → ℝ) x
  map_add' g g' := by
    have e : (fun x => f x * ((g + g' : testSub d) : Rd d → ℝ) x) =
        (fun x => f x * (g : Rd d → ℝ) x) + fun x => f x * (g' : Rd d → ℝ) x := by
      funext x; simp [mul_add]
    rw [e, toHsp_add S (isTest_mul hf g.2) (isTest_mul hf g'.2)]
  map_smul' c g := by
    have e : (fun x => f x * ((c • g : testSub d) : Rd d → ℝ) x) =
        c • fun x => f x * (g : Rd d → ℝ) x := by
      funext x; simp; ring
    rw [e, OccupationCompletion.toHsp_smul c (isTest_mul hf g.2)]; rfl

open UniformMeanCutoff (toHsobL) in
/-- **Bilinear extension from the tests** (`integrated_cameron_mean.tex` lines 86-97 at revision
edf7085f (book 1.1.3)): if `‖[fg]‖_{H_sp} ≤ A ‖f‖_{H^s} ‖g‖_{H^s}` for real tests and
`s ≤ 1`, the product extends uniquely to a bounded bilinear map `H^s × H^s → H_sp` with the same
bound. -/
theorem exists_product_map (S : SpData d) {s A : ℝ} (hs1 : s ≤ 1) (hA : 0 ≤ A)
    (hP : ∀ f g : Rd d → ℝ, IsTestFunction f → IsTestFunction g →
      ‖toHsp S (fun x => f x * g x)‖ ≤ A * ‖coord s f‖ * ‖coord s g‖) :
    ∃ P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S, IsFracProduct S s P ∧
      (∀ P' : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S, IsFracProduct S s P' → P' = P) ∧
      ∀ u v, ‖P u v‖ ≤ A * ‖u‖ * ‖v‖ := by
  have he := denseRange_toHsobL (d := d) hs1
  have hbL : ∀ f : testSub d, ∀ g : testSub d,
      ‖mulSpL S f.2 g‖ ≤ (A * ‖toHsobL s f‖) * ‖toHsobL s g‖ := fun f g => by
    have := hP f g f.2 g.2
    rw [mul_assoc] at this ⊢
    exact this
  set L : testSub d → Hsob d s →L[ℝ] Hsp S := fun f => (mulSpL S f.2).extendOfNorm (toHsobL s)
    with hL
  have hLeq : ∀ f g : testSub d, L f (toHsobL s g) = mulSpL S f.2 g := fun f g =>
    LinearMap.extendOfNorm_eq he ⟨_, hbL f⟩ g
  have hLn : ∀ f : testSub d, ‖L f‖ ≤ A * ‖toHsobL s f‖ := fun f =>
    LinearMap.opNorm_extendOfNorm_le he (mul_nonneg hA (norm_nonneg _)) (hbL f)
  have hext : ∀ M M' : Hsob d s →L[ℝ] Hsp S, (∀ g : testSub d, M (toHsobL s g) =
      M' (toHsobL s g)) → M = M' := fun M M' h =>
    ContinuousLinearMap.coeFn_injective (Continuous.ext_on he M.continuous M'.continuous
      (by rintro _ ⟨g, rfl⟩; exact h g))
  have hLadd : ∀ f f' : testSub d, L (f + f') = L f + L f' := fun f f' => hext _ _ fun g => by
    rw [add_apply, hLeq, hLeq, hLeq]
    change toHsp S (fun x => (f + f' : testSub d).1 x * (g : Rd d → ℝ) x) =
      toHsp S (fun x => (f : Rd d → ℝ) x * (g : Rd d → ℝ) x) +
        toHsp S (fun x => (f' : Rd d → ℝ) x * (g : Rd d → ℝ) x)
    have e : (fun x => (f + f' : testSub d).1 x * (g : Rd d → ℝ) x) =
        (fun x => (f : Rd d → ℝ) x * (g : Rd d → ℝ) x) +
          fun x => (f' : Rd d → ℝ) x * (g : Rd d → ℝ) x := by
      funext x; simp [add_mul]
    rw [e, toHsp_add S (isTest_mul f.2 g.2) (isTest_mul f'.2 g.2)]
  have hLsmul : ∀ (c : ℝ) (f : testSub d), L (c • f) = c • L f := fun c f => hext _ _ fun g => by
    rw [smul_apply, hLeq, hLeq]
    change toHsp S (fun x => (c • f : testSub d).1 x * (g : Rd d → ℝ) x) =
      c • toHsp S (fun x => (f : Rd d → ℝ) x * (g : Rd d → ℝ) x)
    have e : (fun x => (c • f : testSub d).1 x * (g : Rd d → ℝ) x) =
        c • fun x => (f : Rd d → ℝ) x * (g : Rd d → ℝ) x := by
      funext x; simp; ring
    rw [e, OccupationCompletion.toHsp_smul c (isTest_mul f.2 g.2)]
  -- for fixed `v`, `f ↦ L f v` on the tests, extended in `f`
  let Nv : Hsob d s → testSub d →ₗ[ℝ] Hsp S := fun v =>
    { toFun := fun f => L f v
      map_add' := fun f f' => by rw [hLadd, add_apply]
      map_smul' := fun c f => by rw [hLsmul, smul_apply]; rfl }
  have hNv : ∀ v (f : testSub d), ‖Nv v f‖ ≤ (A * ‖v‖) * ‖toHsobL s f‖ := fun v f =>
    calc ‖L f v‖ ≤ ‖L f‖ * ‖v‖ := (L f).le_opNorm v
      _ ≤ (A * ‖toHsobL s f‖) * ‖v‖ := mul_le_mul_of_nonneg_right (hLn f) (norm_nonneg _)
      _ = (A * ‖v‖) * ‖toHsobL s f‖ := by ring
  set M : Hsob d s → Hsob d s →L[ℝ] Hsp S := fun v => (Nv v).extendOfNorm (toHsobL s) with hM
  have hMeq : ∀ v (f : testSub d), M v (toHsobL s f) = L f v := fun v f =>
    LinearMap.extendOfNorm_eq he ⟨_, hNv v⟩ f
  have hMn : ∀ v, ‖M v‖ ≤ A * ‖v‖ := fun v =>
    LinearMap.opNorm_extendOfNorm_le he (mul_nonneg hA (norm_nonneg _)) (hNv v)
  have hMadd : ∀ v v', M (v + v') = M v + M v' := fun v v' => hext _ _ fun f => by
    rw [add_apply, hMeq, hMeq, hMeq, map_add]
  have hMsmul : ∀ (c : ℝ) v, M (c • v) = c • M v := fun c v => hext _ _ fun f => by
    rw [smul_apply, hMeq, hMeq, map_smul]
  let Bl : Hsob d s →ₗ[ℝ] Hsob d s →ₗ[ℝ] Hsp S :=
    LinearMap.mk₂ ℝ (fun u v => M v u) (fun u u' v => map_add _ _ _)
      (fun c u v => map_smul _ _ _) (fun u v v' => by rw [hMadd, add_apply])
      (fun c u v => by rw [hMsmul, smul_apply])
  have hBl : ∀ u v, ‖Bl u v‖ ≤ A * ‖u‖ * ‖v‖ := fun u v =>
    calc ‖M v u‖ ≤ ‖M v‖ * ‖u‖ := (M v).le_opNorm u
      _ ≤ (A * ‖v‖) * ‖u‖ := mul_le_mul_of_nonneg_right (hMn v) (norm_nonneg _)
      _ = A * ‖u‖ * ‖v‖ := by ring
  set P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S := Bl.mkContinuous₂ A hBl with hPdef
  have hPapp : ∀ u v, P u v = M v u := fun u v => rfl
  have hfrac : IsFracProduct S s P := fun f g hf hg => by
    rw [hPapp]
    change M (toHsobL s ⟨g, hg⟩) (toHsobL s ⟨f, hf⟩) = _
    rw [hMeq, hLeq]
    rfl
  refine ⟨P, hfrac, fun P' hP' => ?_, fun u v => hBl u v⟩
  refine ContinuousLinearMap.coeFn_injective (Continuous.ext_on he P'.continuous P.continuous ?_)
  rintro _ ⟨f, rfl⟩
  refine hext _ _ fun g => ?_
  change P' (toHsob s f) (toHsob s g) = P (toHsob s f) (toHsob s g)
  rw [hP' _ _ f.2 g.2, hfrac _ _ f.2 g.2]

/-! ### Pairings of products equal the physical integrals -/

section Pairings

variable {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {s K : ℝ}

/-- Auxiliary: a physical function is a.e. strongly measurable. -/
theorem aesm_phys {u : Hsob d s} {f : Rd d → ℝ} (hu : IsPhysRep s u f) :
    AEStronglyMeasurable f volume := by
  obtain ⟨hf, -⟩ := hu
  simpa using hf.aestronglyMeasurable.re

/-- Auxiliary: the product of four physical functions is `ν`-integrable (from the absolute
bound). -/
theorem quad_integrable (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hT : ∀ φ₁ φ₂ φ₃ φ₄ : Rd d → ℝ, IsTestFunction φ₁ → IsTestFunction φ₂ → IsTestFunction φ₃ →
      IsTestFunction φ₄ →
      ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (K * (‖coord s φ₁‖ * ‖coord s φ₂‖ * ‖coord s φ₃‖ * ‖coord s φ₄‖)))
    {u₁ u₂ u₃ u₄ : Hsob d s} {f₁ f₂ f₃ f₄ : Rd d → ℝ} (h₁ : IsPhysRep s u₁ f₁)
    (h₂ : IsPhysRep s u₂ f₂) (h₃ : IsPhysRep s u₃ f₃) (h₄ : IsPhysRep s u₄ f₄) :
    Integrable (fun p : Rd d × Rd d => f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))
      (pairMeasure Γ) :=
  ⟨(((SpatialFourLinear.aesm_fst Γ (aesm_phys h₁)).mul
      (SpatialFourLinear.aesm_fst Γ (aesm_phys h₂))).mul
      (SpatialFourLinear.aesm_sub Γ (aesm_phys h₃))).mul
      (SpatialFourLinear.aesm_sub Γ (aesm_phys h₄)),
    (phys_absolute hs0 hs1 hT h₁ h₂ h₃ h₄).trans_lt ENNReal.ofReal_lt_top⟩

/-- Auxiliary: `|C₄(f₁,f₂,f₃,f₄)| ≤ K ∏ ‖u_j‖` for physical functions. -/
theorem abs_C4_phys_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K)
    (hT : ∀ φ₁ φ₂ φ₃ φ₄ : Rd d → ℝ, IsTestFunction φ₁ → IsTestFunction φ₂ → IsTestFunction φ₃ →
      IsTestFunction φ₄ →
      ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (K * (‖coord s φ₁‖ * ‖coord s φ₂‖ * ‖coord s φ₃‖ * ‖coord s φ₄‖)))
    {u₁ u₂ u₃ u₄ : Hsob d s} {f₁ f₂ f₃ f₄ : Rd d → ℝ} (h₁ : IsPhysRep s u₁ f₁)
    (h₂ : IsPhysRep s u₂ f₂) (h₃ : IsPhysRep s u₃ f₃) (h₄ : IsPhysRep s u₄ f₄) :
    |C4 Γ f₁ f₂ f₃ f₄| ≤ K * (‖u₁‖ * ‖u₂‖ * ‖u₃‖ * ‖u₄‖) := by
  have h := (enorm_integral_le_lintegral_enorm _).trans (phys_absolute hs0 hs1 hT h₁ h₂ h₃ h₄)
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

omit [IsLocallyFiniteMeasure Γ] in
/-- Auxiliary: telescoping `C₄(a) - C₄(b)` (TeX line 374 of the spatial four-linear section,
in integrable form). -/
theorem C4_sub_tele {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : Rd d → ℝ}
    (ia : Integrable (fun p : Rd d × Rd d => a₁ p.1 * a₂ p.1 * a₃ (p.1 - p.2) * a₄ (p.1 - p.2))
      (pairMeasure Γ))
    (ib : Integrable (fun p : Rd d × Rd d => b₁ p.1 * b₂ p.1 * b₃ (p.1 - p.2) * b₄ (p.1 - p.2))
      (pairMeasure Γ))
    (i₁ : Integrable (fun p : Rd d × Rd d =>
      (a₁ p.1 - b₁ p.1) * a₂ p.1 * a₃ (p.1 - p.2) * a₄ (p.1 - p.2)) (pairMeasure Γ))
    (i₂ : Integrable (fun p : Rd d × Rd d =>
      b₁ p.1 * (a₂ p.1 - b₂ p.1) * a₃ (p.1 - p.2) * a₄ (p.1 - p.2)) (pairMeasure Γ))
    (i₃ : Integrable (fun p : Rd d × Rd d =>
      b₁ p.1 * b₂ p.1 * (a₃ (p.1 - p.2) - b₃ (p.1 - p.2)) * a₄ (p.1 - p.2)) (pairMeasure Γ))
    (i₄ : Integrable (fun p : Rd d × Rd d =>
      b₁ p.1 * b₂ p.1 * b₃ (p.1 - p.2) * (a₄ (p.1 - p.2) - b₄ (p.1 - p.2))) (pairMeasure Γ)) :
    C4 Γ a₁ a₂ a₃ a₄ - C4 Γ b₁ b₂ b₃ b₄ =
      C4 Γ (fun x => a₁ x - b₁ x) a₂ a₃ a₄ + C4 Γ b₁ (fun x => a₂ x - b₂ x) a₃ a₄ +
        C4 Γ b₁ b₂ (fun x => a₃ x - b₃ x) a₄ + C4 Γ b₁ b₂ b₃ (fun x => a₄ x - b₄ x) := by
  have e0 : C4 Γ a₁ a₂ a₃ a₄ - C4 Γ b₁ b₂ b₃ b₄ = ∫ p, ((a₁ p.1 - b₁ p.1) * a₂ p.1 *
      a₃ (p.1 - p.2) * a₄ (p.1 - p.2) + b₁ p.1 * (a₂ p.1 - b₂ p.1) * a₃ (p.1 - p.2) *
      a₄ (p.1 - p.2) + b₁ p.1 * b₂ p.1 * (a₃ (p.1 - p.2) - b₃ (p.1 - p.2)) * a₄ (p.1 - p.2) +
      b₁ p.1 * b₂ p.1 * b₃ (p.1 - p.2) * (a₄ (p.1 - p.2) - b₄ (p.1 - p.2))) ∂(pairMeasure Γ) := by
    rw [C4, C4, ← integral_sub ia ib]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    ring
  rw [e0]
  refine (integral_add ((i₁.add i₂).add i₃) i₄).trans ?_
  congr 1
  refine (integral_add (i₁.add i₂) i₃).trans ?_
  congr 1
  exact integral_add i₁ i₂

/-- Auxiliary: on real tests, `⟪[f₁ f₂], [f₃ f₄]⟫_{H_sp} = C₄(f₁,f₂,f₃,f₄)` (Fubini). -/
theorem inner_toHsp_mul (S : SpData d) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hT : ∀ φ₁ φ₂ φ₃ φ₄ : Rd d → ℝ, IsTestFunction φ₁ → IsTestFunction φ₂ → IsTestFunction φ₃ →
      IsTestFunction φ₄ →
      ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure S.Γ) ≤
        ENNReal.ofReal (K * (‖coord s φ₁‖ * ‖coord s φ₂‖ * ‖coord s φ₃‖ * ‖coord s φ₄‖)))
    {f₁ f₂ f₃ f₄ : Rd d → ℝ} (h₁ : IsTestFunction f₁) (h₂ : IsTestFunction f₂)
    (h₃ : IsTestFunction f₃) (h₄ : IsTestFunction f₄) :
    ⟪toHsp S (fun x => f₁ x * f₂ x), toHsp S (fun x => f₃ x * f₄ x)⟫ = C4 S.Γ f₁ f₂ f₃ f₄ := by
  rw [OccupationCompletion.inner_toHsp (isTest_mul h₁ h₂) (isTest_mul h₃ h₄),
    SpatialFourierBound.spatialPair]
  have hi := quad_integrable (Γ := S.Γ) hs0 hs1 hT (isPhysRep_test s h₁) (isPhysRep_test s h₂)
    (isPhysRep_test s h₃) (isPhysRep_test s h₄)
  rw [C4, integral_prod_symm _ hi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- **The Hilbert pairings of products are the physical integrals**
(`integrated_cameron_mean.tex` line 36 and Step 3, lines 86-93, at revision edf7085f (book
1.1.3)): `⟪P(u₁,u₂), P(u₃,u₄)⟫_{H_sp} = C₄(f₁,f₂,f₃,f₄)` for physical functions `f_j` of
`u_j`.  Both sides are limits along test approximants (the left by continuity of `P`, the right
by telescoping and the absolute bound for differences). -/
theorem inner_product_eq_C4 (S : SpData d) {s K : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K)
    (hT : ∀ φ₁ φ₂ φ₃ φ₄ : Rd d → ℝ, IsTestFunction φ₁ → IsTestFunction φ₂ → IsTestFunction φ₃ →
      IsTestFunction φ₄ →
      ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure S.Γ) ≤
        ENNReal.ofReal (K * (‖coord s φ₁‖ * ‖coord s φ₂‖ * ‖coord s φ₃‖ * ‖coord s φ₄‖)))
    {P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S} (hP : IsFracProduct S s P)
    {u₁ u₂ u₃ u₄ : Hsob d s} {f₁ f₂ f₃ f₄ : Rd d → ℝ} (h₁ : IsPhysRep s u₁ f₁)
    (h₂ : IsPhysRep s u₂ f₂) (h₃ : IsPhysRep s u₃ f₃) (h₄ : IsPhysRep s u₄ f₄) :
    ⟪P u₁ u₂, P u₃ u₄⟫ = C4 S.Γ f₁ f₂ f₃ f₄ := by
  obtain ⟨φ₁, t₁, c₁, -⟩ := exists_test_approx hs0 hs1 h₁
  obtain ⟨φ₂, t₂, c₂, -⟩ := exists_test_approx hs0 hs1 h₂
  obtain ⟨φ₃, t₃, c₃, -⟩ := exists_test_approx hs0 hs1 h₃
  obtain ⟨φ₄, t₄, c₄, -⟩ := exists_test_approx hs0 hs1 h₄
  have hcont : Continuous fun q : Hsob d s × Hsob d s => P q.1 q.2 :=
    P.continuous₂
  have hL : Tendsto (fun n => ⟪P (toHsob s (φ₁ n)) (toHsob s (φ₂ n)),
      P (toHsob s (φ₃ n)) (toHsob s (φ₄ n))⟫) atTop (𝓝 ⟪P u₁ u₂, P u₃ u₄⟫) :=
    ((hcont.tendsto (u₁, u₂)).comp (c₁.prodMk_nhds c₂)).inner
      ((hcont.tendsto (u₃, u₄)).comp (c₃.prodMk_nhds c₄))
  have hLeq : ∀ n, ⟪P (toHsob s (φ₁ n)) (toHsob s (φ₂ n)),
      P (toHsob s (φ₃ n)) (toHsob s (φ₄ n))⟫ = C4 S.Γ (φ₁ n) (φ₂ n) (φ₃ n) (φ₄ n) := fun n => by
    rw [hP _ _ (t₁ n) (t₂ n), hP _ _ (t₃ n) (t₄ n)]
    exact inner_toHsp_mul S hs0 hs1 hT (t₁ n) (t₂ n) (t₃ n) (t₄ n)
  -- the bound on `|C₄(φ_n) - C₄(f)|`
  set w₁ : ℕ → Hsob d s := fun n => toHsob s (φ₁ n)
  set w₂ : ℕ → Hsob d s := fun n => toHsob s (φ₂ n)
  set w₃ : ℕ → Hsob d s := fun n => toHsob s (φ₃ n)
  set w₄ : ℕ → Hsob d s := fun n => toHsob s (φ₄ n)
  have hdiff : ∀ n, |C4 S.Γ (φ₁ n) (φ₂ n) (φ₃ n) (φ₄ n) - C4 S.Γ f₁ f₂ f₃ f₄| ≤
      K * (‖w₁ n - u₁‖ * ‖w₂ n‖ * ‖w₃ n‖ * ‖w₄ n‖) + K * (‖u₁‖ * ‖w₂ n - u₂‖ * ‖w₃ n‖ * ‖w₄ n‖) +
        K * (‖u₁‖ * ‖u₂‖ * ‖w₃ n - u₃‖ * ‖w₄ n‖) +
          K * (‖u₁‖ * ‖u₂‖ * ‖u₃‖ * ‖w₄ n - u₄‖) := fun n => by
    have r₁ := isPhysRep_test s (t₁ n)
    have r₂ := isPhysRep_test s (t₂ n)
    have r₃ := isPhysRep_test s (t₃ n)
    have r₄ := isPhysRep_test s (t₄ n)
    have d₁ := isPhysRep_sub r₁ h₁
    have d₂ := isPhysRep_sub r₂ h₂
    have d₃ := isPhysRep_sub r₃ h₃
    have d₄ := isPhysRep_sub r₄ h₄
    rw [C4_sub_tele (quad_integrable hs0 hs1 hT r₁ r₂ r₃ r₄)
      (quad_integrable hs0 hs1 hT h₁ h₂ h₃ h₄)
      (quad_integrable hs0 hs1 hT d₁ r₂ r₃ r₄) (quad_integrable hs0 hs1 hT h₁ d₂ r₃ r₄)
      (quad_integrable hs0 hs1 hT h₁ h₂ d₃ r₄) (quad_integrable hs0 hs1 hT h₁ h₂ h₃ d₄)]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
    · exact abs_C4_phys_le hs0 hs1 hK hT d₁ r₂ r₃ r₄
    · exact abs_C4_phys_le hs0 hs1 hK hT h₁ d₂ r₃ r₄
    · exact abs_C4_phys_le hs0 hs1 hK hT h₁ h₂ d₃ r₄
    · exact abs_C4_phys_le hs0 hs1 hK hT h₁ h₂ h₃ d₄
  have z₁ := tendsto_iff_norm_sub_tendsto_zero.mp c₁
  have z₂ := tendsto_iff_norm_sub_tendsto_zero.mp c₂
  have z₃ := tendsto_iff_norm_sub_tendsto_zero.mp c₃
  have z₄ := tendsto_iff_norm_sub_tendsto_zero.mp c₄
  have n₂ := c₂.norm
  have n₃ := c₃.norm
  have n₄ := c₄.norm
  have hB : Tendsto (fun n =>
      K * (‖w₁ n - u₁‖ * ‖w₂ n‖ * ‖w₃ n‖ * ‖w₄ n‖) + K * (‖u₁‖ * ‖w₂ n - u₂‖ * ‖w₃ n‖ * ‖w₄ n‖) +
        K * (‖u₁‖ * ‖u₂‖ * ‖w₃ n - u₃‖ * ‖w₄ n‖) + K * (‖u₁‖ * ‖u₂‖ * ‖u₃‖ * ‖w₄ n - u₄‖))
      atTop (𝓝 (K * (0 * ‖u₂‖ * ‖u₃‖ * ‖u₄‖) + K * (‖u₁‖ * 0 * ‖u₃‖ * ‖u₄‖) +
        K * (‖u₁‖ * ‖u₂‖ * 0 * ‖u₄‖) + K * (‖u₁‖ * ‖u₂‖ * ‖u₃‖ * 0))) := by
    refine ((tendsto_const_nhds.mul (((z₁.mul n₂).mul n₃).mul n₄)).add
      (tendsto_const_nhds.mul (((tendsto_const_nhds.mul z₂).mul n₃).mul n₄))).add
      (tendsto_const_nhds.mul (((tendsto_const_nhds.mul tendsto_const_nhds).mul z₃).mul n₄))
      |>.add (tendsto_const_nhds.mul (((tendsto_const_nhds.mul tendsto_const_nhds).mul
        tendsto_const_nhds).mul z₄))
  simp only [mul_zero, zero_mul, add_zero] at hB
  have hR : Tendsto (fun n => C4 S.Γ (φ₁ n) (φ₂ n) (φ₃ n) (φ₄ n)) atTop
      (𝓝 (C4 S.Γ f₁ f₂ f₃ f₄)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact hdiff n) hB
  refine tendsto_nhds_unique hL ?_
  simp_rw [hLeq]
  exact hR

end Pairings

/-! ### The Γ-dependent bounds and the target -/

/-- Auxiliary: `R_sp ≥ 0` (a supremum of nonnegative ratios, or `0`). -/
theorem Rsp_nonneg (Γ : Measure (Rd d)) (alpha : ℝ) : 0 ≤ Rsp Γ alpha := by
  refine Real.sSup_nonneg fun r hr => ?_
  obtain ⟨f, g, -, rfl⟩ := hr
  exact div_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)

/-- **`E:cameron-fractional-absolute` on tests under `H:homog`** with `R = R_sp`: for `Γ ≠ 0`
from `test_absolute` with `P:spatial-four-linear` (`R_sp = R_0`, the square bound with the
density of tests in `H¹` of `H1Density`); for `Γ = 0` the pair measure is zero. -/
theorem core_bounds {alpha alpha0 s : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hs : alpha / 4 < s) :
    ∀ φ₁ φ₂ φ₃ φ₄ : Rd d → ℝ, IsTestFunction φ₁ → IsTestFunction φ₂ → IsTestFunction φ₃ →
      IsTestFunction φ₄ →
      ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (Cs alpha s ^ 4 * Rsp Γ alpha *
          (‖coord s φ₁‖ * ‖coord s φ₂‖ * ‖coord s φ₃‖ * ‖coord s φ₄‖)) := by
  intro φ₁ φ₂ φ₃ φ₄ h₁ h₂ h₃ h₄
  have := hH.Γ_radon
  by_cases hΓ : Γ = 0
  · subst hΓ
    simp [pairMeasure, Measure.prod_zero]
  · obtain ⟨hd, ha0, ha2, hne, -, hR0, hB⟩ :=
      SpatialFourLinear.squareBound_R0 hH hΓ (H1Density.h1TestDense d)
    rw [(SpatialFourLinear.Rsp_eq_R0 hd hB hne hR0.le).2.2.2]
    exact test_absolute ha0.le (by linarith) hs hB hR0.le h₁ h₂ h₃ h₄

/-- **`L:cameron-fractional-products`** (`integrated_cameron_mean.tex` lines 29-42, proof lines
44-99, at revision edf7085f (book 1.1.3)): for `α/4 < s < 1/2` there is `C_s ≥ 0`
(depending on `α`, `s` only) such that, for every covariance of `H:homog` with spatial exponent
`α`, the product of real `H^s` functions is a unique bounded bilinear map `P : H^s × H^s → H_sp`
with `‖P(u,v)‖ ≤ C_s² √R_sp ‖u‖ ‖v‖` (`E:cameron-fractional-product`), whose Hilbert pairings
are the physical integrals `C₄` and which satisfies `E:cameron-fractional-absolute`. -/
theorem cameron_fractional_products {alpha s : ℝ} (hs : alpha / 4 < s) (hs' : s < 1 / 2) :
    FractionalProductsTarget d alpha s := by
  refine ⟨Cs alpha s, Cs_nonneg _ _, fun alpha0 Γ μ hH => ?_⟩
  have := hH.Γ_radon
  obtain ⟨-, ha0, -, -⟩ := SpatialSmoothRatio.homog_consequences hH
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hR := Rsp_nonneg Γ alpha
  have hC := Cs_nonneg alpha s
  have hK : 0 ≤ Cs alpha s ^ 4 * Rsp Γ alpha := by positivity
  have hT := core_bounds hH hs
  set S := SpData.ofHomog hH with hS
  have hTS : ∀ φ₁ φ₂ φ₃ φ₄ : Rd d → ℝ, IsTestFunction φ₁ → IsTestFunction φ₂ →
      IsTestFunction φ₃ → IsTestFunction φ₄ →
      ∫⁻ p, ‖φ₁ p.1 * φ₂ p.1 * φ₃ (p.1 - p.2) * φ₄ (p.1 - p.2)‖ₑ ∂(pairMeasure S.Γ) ≤
        ENNReal.ofReal (Cs alpha s ^ 4 * Rsp Γ alpha *
          (‖coord s φ₁‖ * ‖coord s φ₂‖ * ‖coord s φ₃‖ * ‖coord s φ₄‖)) := hT
  have hprod : ∀ f g : Rd d → ℝ, IsTestFunction f → IsTestFunction g →
      ‖toHsp S (fun x => f x * g x)‖ ≤ Cs alpha s ^ 2 * √(Rsp Γ alpha) * ‖coord s f‖ *
        ‖coord s g‖ := fun f g hf hg => by
    have hA : 0 ≤ Cs alpha s ^ 2 * √(Rsp Γ alpha) * ‖coord s f‖ * ‖coord s g‖ := by positivity
    have hsq : ‖toHsp S (fun x => f x * g x)‖ ^ 2 ≤
        (Cs alpha s ^ 2 * √(Rsp Γ alpha) * ‖coord s f‖ * ‖coord s g‖) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_toHsp_mul S hs0 hs1 hTS hf hg hf hg]
      calc C4 S.Γ f g f g ≤ |C4 S.Γ f g f g| := le_abs_self _
        _ ≤ Cs alpha s ^ 4 * Rsp Γ alpha * (‖toHsob (d := d) s f‖ * ‖toHsob (d := d) s g‖ *
              ‖toHsob (d := d) s f‖ * ‖toHsob (d := d) s g‖) :=
            abs_C4_phys_le hs0 hs1 hK hTS (isPhysRep_test s hf) (isPhysRep_test s hg)
              (isPhysRep_test s hf) (isPhysRep_test s hg)
        _ = (Cs alpha s ^ 2 * √(Rsp Γ alpha) * ‖coord s f‖ * ‖coord s g‖) ^ 2 := by
            rw [UniformMeanCutoff.norm_toHsob, UniformMeanCutoff.norm_toHsob]
            rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hR]
            ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hA two_ne_zero).mp hsq
  obtain ⟨P, hfrac, huniq, hbound⟩ :=
    exists_product_map S hs1 (A := Cs alpha s ^ 2 * √(Rsp Γ alpha)) (by positivity) hprod
  exact ⟨P, hfrac, huniq, hbound, fun u₁ u₂ u₃ u₄ f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ =>
    ⟨inner_product_eq_C4 S hs0 hs1 hK hTS hfrac h₁ h₂ h₃ h₄,
      phys_absolute hs0 hs1 hTS h₁ h₂ h₃ h₄⟩⟩

end StratonovichHAMSecondMoment.CameronProducts
