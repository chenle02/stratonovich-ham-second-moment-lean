/-
Refutation for the first display of `E:riesz-two` (main TeX lines 5131-5134 at
39f2597a: `E X_2 = c_α t^β/((1-α)(2-α-α₀)(3-α-α₀)(4-α-α₀))`), package theorem
`StratonovichHAMSecondMoment.OrderTwoDiagrams.riesz_self_two_zero`.

Wrong variant: the static (`α₀ = 0`) denominators `(1-α)(2-α)(3-α)(4-α)` kept
at `α₀ > 0` (dropping the time covariance from the Beta integral).
Counterexample: `c = 1`, `α = α₀ = 1/2`, `t = 1`: the diagram is `1/3`, while the
variant gives `16/105`.  `rieszStaticDenominator_contrast` is the package value
at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OrderTwoDiagrams

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel OrderTwoDiagrams

namespace Refutations.OrderTwoDiagrams

/-- The package: at `c = 1`, `α = α₀ = 1/2`, `t = 1` the `(2,0)` Riesz diagram is
`1/3`. -/
theorem rieszStaticDenominator_contrast :
    ∀ D ∈ Pi2 2 0, diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2)
      2 0 D 1 = ENNReal.ofReal (1 / 3) := by
  intro D hD
  rw [riesz_self_two_zero hD zero_le_one (by norm_num) (by norm_num) zero_le_one,
    Real.one_rpow]
  congr 1
  norm_num

/-- The static denominators are false at `α₀ = 1/2`. -/
theorem rieszStaticDenominator_refuted :
    ¬ ∀ D ∈ Pi2 2 0, diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2)
      2 0 D 1 = ENNReal.ofReal (1 * (1 : ℝ) ^ (4 - (1 / 2 : ℝ)) /
        ((1 - 1 / 2) * (2 - 1 / 2) * (3 - 1 / 2) * (4 - 1 / 2))) := by
  intro h
  obtain ⟨D, hD⟩ : (Pi2 2 0).Nonempty :=
    Finset.card_pos.1 (by rw [card_Pi2 (m := 2) (n := 0) (k := 1) rfl]; decide)
  have h1 := h D hD
  rw [rieszStaticDenominator_contrast D hD, Real.one_rpow] at h1
  rw [ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1

end Refutations.OrderTwoDiagrams
