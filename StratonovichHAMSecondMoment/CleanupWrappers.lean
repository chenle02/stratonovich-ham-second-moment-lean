module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item W (the deferred wrappers; approved by Le on 2026-11-22 with the default answers to
all thirteen decisions).  Every target of item W in `MildInterface` (frozen at `59a77ae`) is
proved here by composing the L19 wrappers of `SourceFinal` with the library lemmas named in
`docs/l20/INTERFACE.md`, section 2 (W).  TeX lines refer to
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f (book 1.1.3).

Contents.
* The frozen W theorems with the frozen names and statements (the Riesz ones take the hypothesis
  `hR : RieszInstanceTarget`, as frozen).
* `riesz_instance_l20 : RieszInstanceTarget`, from item R's `riesz_homogCovariance_one`
  (`RieszInstanceOne`, merged from `wave-l20/r` at `873ce87`, TeX 5317-5322 with 384-401).
* The hypothesis-free Riesz forms (`…_closed_l20`): the frozen Riesz theorems with `hR`
  discharged by `riesz_instance_l20`.  These close the `hH` that the L19 wrappers
  `d1_upper_paper_l19`, `first_calibration_riesz_paper_l19` added and `riesz_small_paper_l19`
  kept from `RieszFourDiagrams.riesz_small_paper'`.

Route (as INTERFACE.md section 2, W): `E:low-alpha-coefficient`'s second inequality (TeX
5727-5733) is `D1Upper.div_le_div_factorial` with `b = 2 - α` (as in
`D1Upper.d1_upper_paper_riesz`);
the conditional clause of `C:d1-first-calibration` (TeX 5839-5841) is
`LowAlphaUpper.lower_rate_le` applied to the upper bound of the first-calibration wrapper;
`ρ > κ` (TeX 2369, 2431-2432) from `β - 1 = 3 - α - α₀ < 3 - α` with `β = 4 - α - α₀ > 0`
(`hH.threshold`, `hH.alpha0_pos`); `E:envelope-growth` (TeX 2366-2370) from
`HomogeneousEnvelope.envelope_growth` with `β/(β-1)` rewritten as `(4-α-α₀)/(3-α-α₀)`.
No route difference from the TeX.  No instance is declared.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface
public import StratonovichHAMSecondMoment.RieszInstanceOne

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.CleanupWrappers

universe u

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (specV)
open SourceInterface
open HomogeneousEnvelope (BK)
open LowAlphaUpper (C1 C2 Kgen kappa)
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
open MildInterface

/-! ### `P:d1-upper` (TeX 5454-5466) -/

/-- **`P:d1-upper`, white case** (TeX 5454-5466 with 5320 at revision edf7085f (book 1.1.3)),
`Γ = c δ₀`: `D1Upper.d1_upper_paper_white` with `MixedMoment` discharged by
`SourceFinal.mixed_terms_l19` (`H:homog` by `WhiteModel.white_homogCovariance`). -/
theorem d1_upper_paper_white_l20 : D1UpperWhiteTarget.{u} :=
  fun h0 h1 hc ht _ _ P _ W hW x =>
    D1Upper.d1_upper_paper_white h0 h1 hc ht
      (SourceFinal.mixed_terms_l19 1 (WhiteModel.white_homogCovariance hc.le h0 h1) P W hW _ ht x)

/-- **`P:d1-upper`, Riesz case** (TeX 5454-5466 with 5319 at revision edf7085f (book 1.1.3)):
`SourceFinal.d1_upper_paper_l19` with its `hH` supplied by `hR`. -/
theorem d1_upper_paper_l20 (hR : RieszInstanceTarget) : D1UpperRieszTarget.{u} :=
  fun h0 h1 hc ha0 ha1 ht _ _ _ _ _ hW x =>
    SourceFinal.d1_upper_paper_l19 (hR h0 h1 hc ha0 ha1).choose_spec h0 h1 hc ha0 ha1 ht hW x

/-! ### `P:riesz-small` (TeX 5125-5172) -/

/-- **`P:riesz-small`, order-two part `E:riesz-two`** (TeX 5125-5172, display 5129-5142, at
revision edf7085f (book 1.1.3)):
`SourceFinal.riesz_small_paper_l19` with its `hH` supplied by `hR`. -/
theorem riesz_small_paper_l20 (hR : RieszInstanceTarget) : RieszSmallTarget.{u} :=
  fun hc ha ha1 h0 h1 _ _ _ _ _ hW _ ht x =>
    SourceFinal.riesz_small_paper_l19 (hR h0 h1 hc ha ha1).choose_spec hc ha ha1 h0 h1 hW ht x

/-! ### `C:d1-first-calibration` (TeX 5830-5842) -/

/-- **`C:d1-first-calibration`, Riesz case** (TeX 5830-5842 at revision edf7085f (book 1.1.3)):
`SourceFinal.first_calibration_riesz_paper_l19` with its `hH` supplied by `hR`. -/
theorem first_calibration_riesz_paper_l20 (hR : RieszInstanceTarget) :
    FirstCalibrationRieszTarget.{u} :=
  fun hc ha ha1 h0 h1 _ _ _ _ _ hW _ ht x =>
    SourceFinal.first_calibration_riesz_paper_l19 (hR h0 h1 hc ha ha1).choose_spec hc ha ha1 h0 h1
      hW ht x

/-- **The conditional rate clause of `C:d1-first-calibration`** (TeX 5839-5841 at revision
edf7085f (book 1.1.3)), under `H:homog`, `α ≤ 1`, `V > 0`: a first-moment lower rate `L`
(`exp(L' t^κ) ≤ E u(t,x)` eventually, for every `L' < L`) satisfies `2L ≤ 2C_{1,*} < C_{2,*}`.
`LowAlphaUpper.lower_rate_le` against the upper bound `E u ≤ exp(C_{1,*} t^κ)` of
`SourceFinal.first_calibration_paper_l19`. -/
theorem first_calibration_rate_l20 (d : ℕ) : FirstCalibrationRateTarget.{u} d := by
  intro α α₀ Γ μ hH hα1 hV Ω _ P _ W hW x L hlow
  have hup : ∀ t : ℝ, 0 < t → firstMean hW x t ≤
      Real.exp (C1 α α₀ (Kgen α (specV μ).toReal) * t ^ kappa α α₀) := fun t ht => by
    unfold firstMean
    rw [dite_eq_left ht]
    exact (SourceFinal.first_calibration_paper_l19 hH hα1 hV hW ht x).2.1
  have h1 := LowAlphaUpper.lower_rate_le _ hup hlow
  have h2 := (SourceFinal.first_calibration_paper_l19 hH hα1 hV hW one_pos x).2.2.2
  exact ⟨by linarith, h2⟩

/-- **The conditional rate clause of `C:d1-first-calibration`, white case** (TeX 5839-5841 at
revision edf7085f (book 1.1.3)), `Γ = c δ₀`: `2L ≤ 2C_{1,*} < C_{2,*}` with `K = c`, from
`SourceFinal.first_calibration_white_paper_l19` and `LowAlphaUpper.lower_rate_le`. -/
theorem first_calibration_rate_white_l20 : FirstCalibrationRateWhiteTarget.{u} := by
  intro c α₀ hc h0 h1 Ω _ P _ W hW x L hlow
  have hup : ∀ t : ℝ, 0 < t → firstMean hW x t ≤ Real.exp (C1 1 α₀ c * t ^ kappa 1 α₀) :=
    fun t ht => by
      unfold firstMean
      rw [dite_eq_left ht]
      exact (SourceFinal.first_calibration_white_paper_l19 hc h0 h1 hW ht x).2.1
  have h1' := LowAlphaUpper.lower_rate_le _ hup hlow
  have h2 := (SourceFinal.first_calibration_white_paper_l19 hc h0 h1 hW one_pos x).2.2.2
  exact ⟨by linarith, h2⟩

/-- **The conditional rate clause of `C:d1-first-calibration`, Riesz case** (TeX 5839-5841 at
revision edf7085f (book 1.1.3)): `2L ≤ 2C_{1,*} < C_{2,*}` with `K = K_sp(c, α)`, from
`SourceFinal.first_calibration_riesz_paper_l19` (its `hH` supplied by `hR`) and
`LowAlphaUpper.lower_rate_le`. -/
theorem first_calibration_rate_riesz_l20 (hR : RieszInstanceTarget) :
    FirstCalibrationRateRieszTarget.{u} := by
  intro c α α₀ hc ha ha1 h0 h1 Ω _ P _ W hW x L hlow
  have hH := (hR h0 h1 hc ha ha1).choose_spec
  have hup : ∀ t : ℝ, 0 < t → firstMean hW x t ≤
      Real.exp (C1 α α₀ (Ksp c α) * t ^ kappa α α₀) := fun t ht => by
    unfold firstMean
    rw [dite_eq_left ht]
    exact (SourceFinal.first_calibration_riesz_paper_l19 hH hc ha ha1 h0 h1 hW ht x).2.1
  have h1' := LowAlphaUpper.lower_rate_le _ hup hlow
  have h2 := (SourceFinal.first_calibration_riesz_paper_l19 hH hc ha ha1 h0 h1 hW one_pos x).2.2.2
  exact ⟨by linarith, h2⟩

/-! ### `P:low-alpha-upper` (TeX 5711-5734) -/

/-- **`P:low-alpha-upper`, both inequalities of `E:low-alpha-coefficient`** (TeX 5711-5734,
display 5727-5733, at revision edf7085f (book 1.1.3)), under `H:homog`, `α ≤ 1`, `V > 0`:
`SourceFinal.low_alpha_upper_moment_paper_l19` (first inequality and the second-moment bound);
the second inequality `Q/(k! k^{bk}) ≤ Q/(k!)^q`, `b = 2 - α`, `q = b + 1 = 3 - α`, is
`D1Upper.div_le_div_factorial` (`b ≥ 0` from `α ≤ 1`). -/
theorem low_alpha_upper_moment_paper_l20 (d : ℕ) : LowAlphaUpperTarget.{u} d := by
  intro α α₀ Γ μ hH hα1 hV Ω _ P _ W hW t ht x
  have hL := SourceFinal.low_alpha_upper_moment_paper_l19 hH hα1 hV hW ht x
  refine ⟨fun k hk => ⟨hL.1 k hk, ?_⟩, hL.2⟩
  have hQ : 0 ≤ (2 * Zc α₀ * Kgen α (specV μ).toReal) ^ k * t ^ ((4 - α - α₀) * k) :=
    mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two
      (TwoSimplexTime.Zc_pos hH.alpha0_lt_one).le) (LowAlphaUpper.Kgen_nonneg hV.le)) _)
      (Real.rpow_nonneg ht.le _)
  have := D1Upper.div_le_div_factorial hQ (b := 2 - α) (by linarith) k
  rwa [show 2 - α + 1 = 3 - α by ring] at this

/-! ### `P:envelope` (TeX 2352-2373, proof to 2433) -/

/-- **`ρ > κ`** (TeX 2369, 2431-2432 at revision edf7085f (book 1.1.3)) under `H:homog`:
`β - 1 = 3 - α - α₀ < 3 - α` and `β = 4 - α - α₀ > 0` (`hH.threshold`, `hH.alpha0_pos`), so
`κ = β/(3 - α) < β/(β - 1) = ρ`. -/
theorem rho_gt_kappa_l20 : RhoGtKappaTarget := by
  intro d alpha α₀ Γ μ hH
  have h0 := hH.alpha0_pos
  have hth := hH.threshold
  unfold kappa
  exact div_lt_div_of_pos_left (by linarith) (by linarith) (by linarith)

/-- **`P:envelope`, d = 1, 2, 3, with `E:envelope-growth`** (TeX 2352-2373, display 2366-2370;
proof 2375-2433, at revision edf7085f (book 1.1.3)): the chaos-term and second-moment bounds of
`SourceFinal.envelope_paper_l19`, the growth `c t^ρ ≤ log B_K(t) ≤ C t^ρ` for large `t` from
`HomogeneousEnvelope.envelope_growth` (`β = 4 - α - α₀ > 2` by `hH.threshold`, and
`β/(β - 1) = (4-α-α₀)/(3-α-α₀)`), and `ρ > κ` (`rho_gt_kappa_l20`).  The lower growth bound
concerns the majorant `B_K`, not the second moment (TeX 2371-2372). -/
theorem envelope_paper_l20 (d : ℕ) : EnvelopeTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨K, hK, hmom⟩ := SourceFinal.envelope_paper_l19.{u} hH
  have hβ : 2 < 4 - alpha - α₀ := by linarith [hH.threshold]
  have hg := HomogeneousEnvelope.envelope_growth hK hβ
  rw [show 4 - alpha - α₀ - 1 = 3 - alpha - α₀ by ring] at hg
  exact ⟨K, hK, fun t ht Ω _ P _ W hW x => hmom t ht P W hW x, hg, rho_gt_kappa_l20 hH⟩

/-! ### The Riesz instance (item R) and the hypothesis-free Riesz forms -/

/-- **`E:d1-covariances` as an instance of `H:homog`** (TeX 5317-5322 with 384-401 and 5315 at
revision edf7085f (book 1.1.3)): item R's `RieszInstanceOne.riesz_homogCovariance_one`. -/
theorem riesz_instance_l20 : RieszInstanceTarget :=
  @RieszInstanceOne.riesz_homogCovariance_one

/-- **`P:d1-upper`, Riesz case, hypothesis-free** (TeX 5454-5466 with 5319 at revision edf7085f
(book 1.1.3)): `d1_upper_paper_l20` with `riesz_instance_l20`. -/
theorem d1_upper_paper_closed_l20 : D1UpperRieszTarget.{u} :=
  d1_upper_paper_l20 riesz_instance_l20

/-- **`P:riesz-small`, order-two part, hypothesis-free** (TeX 5125-5172, display 5129-5142, at
revision edf7085f (book 1.1.3)):
`riesz_small_paper_l20` with `riesz_instance_l20`. -/
theorem riesz_small_paper_closed_l20 : RieszSmallTarget.{u} :=
  riesz_small_paper_l20 riesz_instance_l20

/-- **`C:d1-first-calibration`, Riesz case, hypothesis-free** (TeX 5830-5842 at revision edf7085f
(book 1.1.3)): `first_calibration_riesz_paper_l20` with `riesz_instance_l20`. -/
theorem first_calibration_riesz_paper_closed_l20 : FirstCalibrationRieszTarget.{u} :=
  first_calibration_riesz_paper_l20 riesz_instance_l20

/-- **The conditional rate clause of `C:d1-first-calibration`, Riesz case, hypothesis-free**
(TeX 5839-5841 at revision edf7085f (book 1.1.3)): `first_calibration_rate_riesz_l20` with
`riesz_instance_l20`. -/
theorem first_calibration_rate_riesz_closed_l20 : FirstCalibrationRateRieszTarget.{u} :=
  first_calibration_rate_riesz_l20 riesz_instance_l20

end StratonovichHAMSecondMoment.CleanupWrappers
