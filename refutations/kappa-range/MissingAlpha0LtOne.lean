import StratonovichHAMSecondMoment.KappaRange

/-!
Refutation for `StratonovichHAMSecondMoment.KappaRange.kappa_mem_Ioo`, manuscript label
`E:kappa`.

Wrong variant: `kappa_mem_Ioo` with the hypothesis `α₀ < 1` dropped; the lower bound
`1 < κ` then fails. Counterexample: `d = 1`, `α = 1/4`, `α₀ = 3/2` (so `0 < α₀`,
`α₀ + α < 2`, `0 < α < d`), where the package's `KappaRange.kappa` gives
`κ = 9/11 ≤ 1`. The contrast theorem evaluates the package `kappa` at this point and
records that `α₀ < 1` is the only hypothesis that fails there.

Expected outcome: compiles (refuted).
-/

namespace Refutations.KappaRange

open StratonovichHAMSecondMoment.KappaRange

/-- The lower bound of `kappa_mem_Ioo` fails without `α₀ < 1`. -/
theorem missing_alpha0_lt_one :
    ¬ ∀ (d : ℕ) (alpha alpha0 : ℝ), (d = 1 ∨ d = 2 ∨ d = 3) →
      0 < alpha0 → alpha0 + alpha < 2 →
      ((0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1)) →
      1 < StratonovichHAMSecondMoment.KappaRange.kappa alpha alpha0 := by
  intro h
  have := h 1 (1 / 4) (3 / 2) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num [kappa] at this

/-- Contrast: at the counterexample the package `kappa` equals `9/11`, and the dropped
hypothesis `α₀ < 1` is the one that fails there. -/
theorem missing_alpha0_lt_one_contrast :
    StratonovichHAMSecondMoment.KappaRange.kappa (1 / 4) (3 / 2) = 9 / 11 ∧
      ¬ ((3 / 2 : ℝ) < 1) := by
  refine ⟨?_, by norm_num⟩
  norm_num [kappa]

end Refutations.KappaRange
