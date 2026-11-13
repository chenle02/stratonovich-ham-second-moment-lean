import StratonovichHAMSecondMoment.DriverParameters

/-!
Refutation for `StratonovichHAMSecondMoment.DriverParameters.theta_beta_interval_nonempty`
(and hence `parameters_nonempty`), manuscript label `E:driver-parameters`.

Wrong variant: the hypothesis `Homog d alpha a` with its conjunct `a < 1` relaxed to
`a ≤ 1`. At `d = 1`, `α = 1/2`, `a = 1` (so `a + α < 2` and `0 < α < d` still hold)
the `(θ, β)`-interval `1/2 < θ < β < min(1 - a/2, (3-a-α)/2)` is empty, because
`1 - a/2 = 1/2`. The contrast theorem shows that every other conjunct of
`DriverParameters.Homog` holds at this point and that `Homog 1 (1/2) 1` itself fails,
using the package theorem.

This is strictly more faithful than the earlier version, which only stated the empty
interval at the point; the emptiness at the point is the core of the proof.

Expected outcome: compiles (refuted).
-/

namespace Refutations.DriverParameters

open StratonovichHAMSecondMoment.DriverParameters

/-- At `a = 1`, `α = 1/2` the `(θ, β)`-interval of the package theorem is empty. -/
theorem theta_beta_empty_at_a_one :
    ¬ ∃ θ β : ℝ, 1 / 2 < θ ∧ θ < β ∧
      β < min (1 - (1 : ℝ) / 2) ((3 - 1 - 1 / 2) / 2) := by
  rintro ⟨θ, β, h1, h2, h3⟩
  have := min_le_left (1 - (1 : ℝ) / 2) ((3 - 1 - 1 / 2) / 2)
  linarith

/-- `theta_beta_interval_nonempty` with `a < 1` relaxed to `a ≤ 1` in `Homog` is false. -/
theorem a_le_one_variant :
    ¬ (∀ (d : ℕ) (alpha a : ℝ),
      ((d = 1 ∨ d = 2 ∨ d = 3) ∧ 0 < a ∧ a ≤ 1 ∧ a + alpha < 2 ∧
        ((0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1))) →
      ∃ θ β : ℝ, 1 / 2 < θ ∧ θ < β ∧ β < min (1 - a / 2) ((3 - a - alpha) / 2)) := by
  intro h
  exact theta_beta_empty_at_a_one
    (h 1 (1 / 2) 1 ⟨Or.inl rfl, by norm_num, le_rfl, by norm_num,
      Or.inl ⟨by norm_num, by norm_num⟩⟩)

/-- Contrast: at `d = 1`, `α = 1/2`, `a = 1` every conjunct of `Homog` except `a < 1`
holds, and `Homog 1 (1/2) 1` fails, by the package theorem
`theta_beta_interval_nonempty`. -/
theorem a_le_one_variant_contrast :
    ((1 : ℕ) = 1 ∨ (1 : ℕ) = 2 ∨ (1 : ℕ) = 3) ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) + 1 / 2 < 2 ∧
      ((0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < ((1 : ℕ) : ℝ)) ∨
        ((1 / 2 : ℝ) = ((1 : ℕ) : ℝ) ∧ (1 : ℕ) = 1)) ∧
      ¬ Homog 1 (1 / 2) 1 :=
  ⟨Or.inl rfl, by norm_num, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩,
    fun hH => theta_beta_empty_at_a_one
      (StratonovichHAMSecondMoment.DriverParameters.theta_beta_interval_nonempty
        1 (1 / 2) 1 hH)⟩

end Refutations.DriverParameters
