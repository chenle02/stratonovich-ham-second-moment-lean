import StratonovichHAMSecondMoment.KappaRange

/-!
Refutation for `StratonovichHAMSecondMoment.KappaRange.kappa_mem_Ioo`, manuscript label
`E:kappa`.

Wrong variant: `kappa_mem_Ioo` with the threshold hypothesis `α₀ + α < 2`
(`E:threshold`) dropped; the upper bound `κ < 2` then fails. Counterexample: `d = 3`,
`α = 5/2`, `α₀ = 1/10` (so `0 < α₀ < 1`, `0 < α < d`), where the package's
`KappaRange.kappa` gives `κ = 14/5 ≥ 2`. The contrast theorem evaluates the package
`kappa` at this point and records that `α₀ + α < 2` is the only hypothesis that fails
there.

Expected outcome: compiles (refuted).
-/

namespace Refutations.KappaRange

open StratonovichHAMSecondMoment.KappaRange

/-- The upper bound of `kappa_mem_Ioo` fails without `α₀ + α < 2`. -/
theorem missing_threshold :
    ¬ ∀ (d : ℕ) (alpha alpha0 : ℝ), (d = 1 ∨ d = 2 ∨ d = 3) →
      0 < alpha0 → alpha0 < 1 →
      ((0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1)) →
      StratonovichHAMSecondMoment.KappaRange.kappa alpha alpha0 < 2 := by
  intro h
  have := h 3 (5 / 2) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num [kappa] at this

/-- Contrast: at the counterexample the package `kappa` equals `14/5`, and the dropped
hypothesis `α₀ + α < 2` is the one that fails there. -/
theorem missing_threshold_contrast :
    StratonovichHAMSecondMoment.KappaRange.kappa (5 / 2) (1 / 10) = 14 / 5 ∧
      ¬ ((1 / 10 : ℝ) + 5 / 2 < 2) := by
  refine ⟨?_, by norm_num⟩
  norm_num [kappa]

end Refutations.KappaRange
