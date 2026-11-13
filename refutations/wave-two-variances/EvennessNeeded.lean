/-
Refutation for dropping the evenness of `ν_R` in the output direction of
`P:wave-two-variances` (`notes/integrated_wave_variance.tex` at a284420, lines 446-450:
"Reflect `λ` using the evenness of `ν_R` and then use symmetry of `Φ_h`. This row becomes
`∫ Φ_h(η, η-λ) ν_R(dλ)`"), package definition `FrequencyRow.rowKernel` and package
theorem `StratonovichHAMSecondMoment.WaveTwoVariances.rowKernel_symm`.

Wrong variant: the reflection step without evenness, i.e. for every finite measure `ν`
on `ℝ¹` and every `η`, `∫ Φ_h(η+λ, η) ν(dλ) ≤ ∫ Φ_h(η, η-λ) ν(dλ)`. With `a = 1/2`,
`h = 1`, `x` the unit vector, `ν = δ_x` and `η = -x`: the left side is `Φ_1(0, -x) =
2⟨1⟩^{-1/2}/⟨1⟩`, the right side is `Φ_1(-x, -2x) = (⟨1⟩^{-1/2} + ⟨3⟩^{-1/2})/(⟨1⟩⟨2⟩)`,
which is strictly smaller. No junk value is involved (every bracket is `≥ 1`, every
`rpow` has a positive base).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveTwoVariances

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment.MaskedTrigProducts (bracket frequencyPair)
open StratonovichHAMSecondMoment.FrequencyRow (rowKernel bracket_pos one_le_bracket)
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)
open StratonovichHAMSecondMoment.WaveTwoVariances (rowKernel_symm)

namespace Refutations.WaveTwoVariances

/-- The unit vector of `ℝ¹`. -/
noncomputable def e1 : Rd 1 := EuclideanSpace.single 0 1

/-- `‖e₁‖ = 1`. -/
theorem norm_e1 : ‖e1‖ = 1 := by simp [e1]

/-- The strict comparison of the two rows at the counterexample. -/
theorem row_strict :
    rowKernel (1 / 2) 1 (-e1) (-e1 - e1) < rowKernel (1 / 2) 1 (-e1 + e1) (-e1) := by
  have h2 : ‖-e1 - e1‖ = 2 := by
    rw [show -e1 - e1 = (-2 : ℝ) • e1 by module, norm_smul, norm_e1]; norm_num
  unfold rowKernel frequencyPair
  rw [neg_add_cancel, norm_zero, norm_neg, norm_e1, h2]
  have hb1 := bracket_pos 1
  have hb0 : bracket 0 = 1 := by simp [bracket]
  have hb2 : 1 < bracket 2 := by
    unfold bracket; rw [Real.lt_sqrt zero_le_one]; norm_num
  have hb3 : bracket (-1) = bracket 1 := by
    rw [StratonovichHAMSecondMoment.MaskedTrigProducts.bracket_neg]
  have hm : bracket 3 ^ ((1 / 2 : ℝ) - 1) ≤ bracket 1 ^ ((1 / 2 : ℝ) - 1) := by
    refine Real.rpow_le_rpow_of_nonpos hb1 ?_ (by norm_num)
    unfold bracket; exact Real.sqrt_le_sqrt (by norm_num)
  have hp : 0 < bracket 1 ^ ((1 / 2 : ℝ) - 1) := Real.rpow_pos_of_pos hb1 _
  have hp3 : 0 < bracket 3 ^ ((1 / 2 : ℝ) - 1) := Real.rpow_pos_of_pos (bracket_pos 3) _
  norm_num only [mul_one, one_mul, zero_sub, zero_add, hb0, hb3]
  norm_num only at hm hp hp3
  rw [div_lt_div_iff₀ (mul_pos hb1 (lt_trans one_pos hb2)) hb1]
  nlinarith [mul_lt_mul_of_pos_left hb2 (mul_pos hb1 hp)]

/-- Without evenness the reflection of the row integral fails. -/
theorem reflection_without_evenness_fails :
    ¬ ∀ (ν : Measure (Rd 1)), IsFiniteMeasure ν → ∀ η : Rd 1,
      ∫⁻ l, ENNReal.ofReal (rowKernel (1 / 2) 1 (η + l) η) ∂ν ≤
        ∫⁻ l, ENNReal.ofReal (rowKernel (1 / 2) 1 η (η - l)) ∂ν := by
  intro hwrong
  have := hwrong (Measure.dirac e1) inferInstance (-e1)
  rw [lintegral_dirac, lintegral_dirac] at this
  exact absurd ((ENNReal.ofReal_le_ofReal_iff (StratonovichHAMSecondMoment.FrequencyRow.rowKernel_nonneg
    _ _ _ _)).1 this) (not_le.2 row_strict)

/-- Contrast: the reflection that does hold for every measure is the symmetry of `Φ_h`,
`Φ_h(η+λ, η) = Φ_h(η, η+λ)` (package theorem at the counterexample). -/
theorem symmetry_contrast :
    rowKernel (1 / 2) 1 (-e1 + e1) (-e1) = rowKernel (1 / 2) 1 (-e1) (-e1 + e1) :=
  rowKernel_symm _ _ _ _

end Refutations.WaveTwoVariances
