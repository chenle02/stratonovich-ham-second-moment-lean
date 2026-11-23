import StratonovichHAMSecondMoment.L10Completed

/-!
Refutation for the lower bound `0 ≤ ∫ G_{h,η}(dy) γ_ε(y+z)` of `E:alpha-one-convolution`
(`L:alpha-one-convolution`, main TeX lines 5635-5643 at edf7085f; the lemma has no `Γ ≠ 0`),
package theorem
`StratonovichHAMSecondMoment.L10Completed.alpha_one_convolution_paper_completed`.

Wrong variant: strict positivity `0 < ∫ G_{h,η}(dy) γ_ε(y+z)` under `H:homog` with `α = 1`.
Witness: `d = 2`, `α₀ = 1/2`, `Γ = μ = 0`, which satisfies every field of `H:homog`
(`0 < α = 1 < d = 2`, `α₀ + α < 2`); then `γ_ε = 0` and the pairing is `0`, so the lower bound
is attained.  The value `0` is the genuine integral of the zero function (the completed theorem
proves integrability), not a junk value.  The contrast theorem applies the completed theorem at
the witness and computes the pairing.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.L10Completed

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HomogHypothesis

/-- `Γ = μ = 0` satisfies `H:homog` in `d = 2` with `α = 1`, `α₀ = 1/2`. -/
theorem zero_homog : HomogCovariance 2 1 (1 / 2) (0 : Measure (Rd 2)) 0 where
  dim := Or.inr (Or.inl rfl)
  alpha0_pos := by norm_num
  alpha0_lt_one := by norm_num
  Γ_radon := inferInstance
  Γ_even := by unfold IsEven; simp
  Γ_tempered := ⟨0, by simp⟩
  Γ_posdef := fun φ => by simp
  μ_radon := inferInstance
  μ_even := by unfold IsEven; simp
  μ_tempered := ⟨0, by simp⟩
  spectral := fun φ => by simp
  scaling := fun A _ c _ => by simp
  threshold := by norm_num
  alpha_range := Or.inl ⟨by norm_num, by norm_num⟩

/-- Contrast: at the witness the completed theorem gives `0 ≤ pairing`, and the pairing is `0`
(`h = ε = η = 1`, `z = 0`). -/
theorem strict_positivity_contrast :
    0 ≤ ∫ y, VariationalDilation.conv (0 : Measure (Rd 2)) (VariationalMean.heatK 1) (y + 0)
        ∂(LowAlphaConvolution.smoothedGreen (WaveGreen.waveGreen 2) 1 1) ∧
      ∫ y, VariationalDilation.conv (0 : Measure (Rd 2)) (VariationalMean.heatK 1) (y + 0)
        ∂(LowAlphaConvolution.smoothedGreen (WaveGreen.waveGreen 2) 1 1) = 0 := by
  refine ⟨((L10Completed.alpha_one_convolution_paper_completed zero_homog).2 1 one_pos 1
    one_pos 1 zero_le_one 0).2.2.2.2.1, ?_⟩
  simp [VariationalDilation.conv]

/-- Strict positivity of the pairing under `H:homog` with `α = 1` is false. -/
theorem strict_positivity :
    ¬ ∀ Γ μ : Measure (Rd 2), HomogCovariance 2 1 (1 / 2) Γ μ →
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd 2,
        0 < ∫ y, VariationalDilation.conv Γ (VariationalMean.heatK ε) (y + z)
          ∂(LowAlphaConvolution.smoothedGreen (WaveGreen.waveGreen 2) h η) := by
  intro H
  have := H 0 0 zero_homog 1 one_pos 1 one_pos 1 zero_le_one 0
  rw [strict_positivity_contrast.2] at this
  exact lt_irrefl _ this

end Refutations.L10Completed
