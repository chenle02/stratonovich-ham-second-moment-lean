/-
Refutation for the temporal kernel of `DiagramModel` (the factor
`∏_{(j,h) ∈ D} |s_j - s_h|^{-α₀}` of `E:mixed-diagram`, main TeX line 822 at
39f2597a, from the temporal covariance `|s - t|^{-α₀}` of `E:cov`, line 379),
package definitions `StratonovichHAMSecondMoment.DiagramModel.timeCov` and
`timeWeight`.

Wrong variant: the temporal weight with the sign of the exponent flipped,
`∏_{(j,h) ∈ D} |s_j - s_h|^{+α₀}` (`wrongTimeWeight`).  Counterexample:
`α₀ = 1/2` (`0 < α₀ < 1`, line 379), one chain of length two (`m = 2`,
`n = 0`) with its only pairing `D = {{1, 2}}` (the self-pairing of
`E:white-test`; 0-based labels `0 ↔ 1`), horizon `t = 1`, and the distinct
positive times `(s_1, s_2) = (1/4, 1/2) ∈ [0,1]^2_<` (line 551).  There the
package weight is `|1/4 - 1/2|^{-1/2} = 2`, the wrong one is `1/2`.  The pairing
is in `Π` and the times are in the open simplex, so the point is a genuine
integrand point of `J_{2,0,D}(1)`; both weights are finite and continuous near
it, so they also differ on a neighbourhood of positive measure (not proved
here).  `timeKernelExponent_contrast` gives the package value, the pairing and
the simplex membership at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance (distinct times, finite weights).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramModel

set_option autoImplicit false

open StratonovichHAMSecondMoment DiagramModel
open scoped ENNReal

namespace Refutations.DiagramModel

/-- The wrong temporal weight `∏_{(j,h) ∈ D} |s_j - s_h|^{+α₀}`. -/
noncomputable def wrongTimeWeight {N : ℕ} (α₀ : ℝ) (D : Fin N → Fin N) (s : Fin N → ℝ) :
    ℝ≥0∞ :=
  ∏ i ∈ openers D, (ENNReal.ofReal |s i - s (D i)|) ^ α₀

/-- The only pairing of the chain of length two: `0 ↔ 1`. -/
def swap01 : Fin (2 + 0) → Fin (2 + 0) := ![1, 0]

/-- The times `(1/4, 1/2)`. -/
noncomputable def times01 : Fin (2 + 0) → ℝ := ![1 / 4, 1 / 2]

theorem openers_swap01 : openers swap01 = {0} := by decide

/-- The package value: `swap01 ∈ Π`, `(1/4, 1/2) ∈ [0,1]^2_<`, and the temporal
weight there is `2`. -/
theorem timeKernelExponent_contrast :
    swap01 ∈ Pi2 2 0 ∧ times01 ∈ twoSimplex 2 0 1 ∧
      timeWeight (1 / 2) swap01 times01 = 2 := by
  refine ⟨mem_Pi2.2 (by decide), fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [times01, predVal, pred]
  · rw [timeWeight, openers_swap01, Finset.prod_singleton, timeCov]
    have h1 : |times01 0 - times01 (swap01 0)| = ((1 / 2 : ℝ) ^ 2) := by
      norm_num [times01, swap01, abs_of_neg]
    rw [h1, ENNReal.ofReal_pow (by norm_num), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_neg_one, ENNReal.ofReal_div_of_pos]

/-- The wrong weight at the same point is `1/2`. -/
theorem wrongTimeWeight_value : wrongTimeWeight (1 / 2) swap01 times01 = 2⁻¹ := by
  rw [wrongTimeWeight, openers_swap01, Finset.prod_singleton]
  have h1 : |times01 0 - times01 (swap01 0)| = ((1 / 2 : ℝ) ^ 2) := by
    norm_num [times01, swap01, abs_of_neg]
  rw [h1, ENNReal.ofReal_pow (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- The temporal weight is not the flipped-exponent weight. -/
theorem timeKernelExponent_refuted :
    ¬ (timeWeight (1 / 2) swap01 times01 = wrongTimeWeight (1 / 2) swap01 times01) := by
  rw [timeKernelExponent_contrast.2.2, wrongTimeWeight_value]
  intro h
  have h' := congrArg ENNReal.toReal h
  norm_num [ENNReal.toReal_inv] at h'

end Refutations.DiagramModel
