import StratonovichHAMSecondMoment.DriverParameters

/-!
Refutation for `StratonovichHAMSecondMoment.DriverParameters.theta_beta_interval_nonempty`
(and hence `parameters_nonempty`), manuscript label `E:driver-parameters`.

Wrong variant: the hypothesis `Homog d alpha a` with its threshold conjunct
`a + α < 2` (`E:threshold`) relaxed to `a + α ≤ 2`. At `d = 2`, `a = 1/2`, `α = 3/2`
(so `a + α = 2`) the bound `(3 - a - α)/2 = 1/2` empties the `(θ, β)`-interval
`1/2 < θ < β < min(1 - a/2, (3-a-α)/2)`. The contrast theorem shows that every other
conjunct of `DriverParameters.Homog` holds at this point and that `Homog 2 (3/2) (1/2)`
itself fails, using the package theorem.

This is strictly more faithful than the earlier version, which only stated the empty
interval at the point; the emptiness at the point is the core of the proof.

Expected outcome: compiles (refuted).
-/

namespace Refutations.DriverParameters

open StratonovichHAMSecondMoment.DriverParameters

/-- At `a = 1/2`, `α = 3/2` the `(θ, β)`-interval of the package theorem is empty. -/
theorem theta_beta_empty_at_threshold :
    ¬ ∃ θ β : ℝ, 1 / 2 < θ ∧ θ < β ∧
      β < min (1 - (1 / 2 : ℝ) / 2) ((3 - 1 / 2 - 3 / 2) / 2) := by
  rintro ⟨θ, β, h1, h2, h3⟩
  have := min_le_right (1 - (1 / 2 : ℝ) / 2) ((3 - 1 / 2 - 3 / 2) / 2)
  linarith

/-- `theta_beta_interval_nonempty` with `a + α < 2` relaxed to `a + α ≤ 2` in `Homog`
is false. -/
theorem threshold_le_variant :
    ¬ (∀ (d : ℕ) (alpha a : ℝ),
      ((d = 1 ∨ d = 2 ∨ d = 3) ∧ 0 < a ∧ a < 1 ∧ a + alpha ≤ 2 ∧
        ((0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1))) →
      ∃ θ β : ℝ, 1 / 2 < θ ∧ θ < β ∧ β < min (1 - a / 2) ((3 - a - alpha) / 2)) := by
  intro h
  exact theta_beta_empty_at_threshold
    (h 2 (3 / 2) (1 / 2) ⟨Or.inr (Or.inl rfl), by norm_num, by norm_num, by norm_num,
      Or.inl ⟨by norm_num, by norm_num⟩⟩)

/-- Contrast: at `d = 2`, `α = 3/2`, `a = 1/2` every conjunct of `Homog` except
`a + α < 2` holds, and `Homog 2 (3/2) (1/2)` fails, by the package theorem
`theta_beta_interval_nonempty`. -/
theorem threshold_le_variant_contrast :
    ((2 : ℕ) = 1 ∨ (2 : ℕ) = 2 ∨ (2 : ℕ) = 3) ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
      ((0 < (3 / 2 : ℝ) ∧ (3 / 2 : ℝ) < ((2 : ℕ) : ℝ)) ∨
        ((3 / 2 : ℝ) = ((2 : ℕ) : ℝ) ∧ (2 : ℕ) = 1)) ∧
      ¬ Homog 2 (3 / 2) (1 / 2) :=
  ⟨Or.inr (Or.inl rfl), by norm_num, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩,
    fun hH => theta_beta_empty_at_threshold
      (StratonovichHAMSecondMoment.DriverParameters.theta_beta_interval_nonempty
        2 (3 / 2) (1 / 2) hH)⟩

end Refutations.DriverParameters
