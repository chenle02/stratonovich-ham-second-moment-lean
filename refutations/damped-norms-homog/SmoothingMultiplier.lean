/-
Refutation for the multiplier part of `E:damped-multiplier-comparison` in
`L:damped-homogeneous-norms` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
826-847 and 912-916), package theorem
`StratonovichHAMSecondMoment.DampedNormsHomog.resolvent_smoothed_le`
(`R_{gμ}(q) ≤ R_μ(q)` for a measurable multiplier `g` with values in `[0,1]`).

Wrong variant: the bound `g ≤ 1` dropped.  Counterexample: `d = 1`,
`μ = δ₀`, `g ≡ 2`, `q = 1`: `R_{gμ}(1) = 2 > 1 = R_μ(1)`.
`smoothing_multiplier_contrast` is the package bound at the same `μ` and `q`
with `g ≡ 1/2`.  No junk-value reliance (`δ₀` is finite, the integrands are
bounded).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DampedNormsHomog

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedNormsHomog
open scoped NNReal

namespace Refutations.DampedNormsHomog

/-- Auxiliary. `R_{cδ₀}(1) = c` for a constant multiplier `c`. -/
theorem resolvent_smoothed_dirac (c : ℝ≥0) :
    SpectralHomog.resolvent (smoothed (Measure.dirac (0 : HomogHypothesis.Rd 1))
      (fun _ => c)) 1 = c := by
  simp [SpectralHomog.resolvent, smoothed, withDensity_const, NNReal.smul_def]

/-- Auxiliary. `R_{δ₀}(1) = 1`. -/
theorem resolvent_dirac :
    SpectralHomog.resolvent (Measure.dirac (0 : HomogHypothesis.Rd 1)) 1 = 1 := by
  simp [SpectralHomog.resolvent]

/-- Smoothing without `g ≤ 1` does not decrease `R`: false. -/
theorem smoothing_multiplier_refuted :
    ¬ (∀ g : HomogHypothesis.Rd 1 → ℝ≥0, Measurable g →
        SpectralHomog.resolvent (smoothed (Measure.dirac 0) g) 1 ≤
          SpectralHomog.resolvent (Measure.dirac (0 : HomogHypothesis.Rd 1)) 1) := by
  intro h
  have h1 := h (fun _ => 2) measurable_const
  rw [resolvent_smoothed_dirac, resolvent_dirac] at h1
  norm_num at h1

/-- The package bound at the same point with `g ≡ 1/2`. -/
theorem smoothing_multiplier_contrast :
    SpectralHomog.resolvent (smoothed (Measure.dirac (0 : HomogHypothesis.Rd 1))
      (fun _ => (1 / 2 : ℝ≥0))) 1 ≤
      SpectralHomog.resolvent (Measure.dirac (0 : HomogHypothesis.Rd 1)) 1 :=
  resolvent_smoothed_le _ _ measurable_const (fun _ => by norm_num)
    (integrable_const (1 : ℝ) |>.mono'
      (Measurable.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact div_le_one_of_le₀ (by nlinarith [sq_nonneg ‖ξ‖]) (by positivity)))
    1 one_ne_zero

end Refutations.DampedNormsHomog
