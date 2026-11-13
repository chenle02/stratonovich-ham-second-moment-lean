import StratonovichHAMSecondMoment.DriverParameters

/-!
Refutation for `StratonovichHAMSecondMoment.DriverParameters.gamma_interval_nonempty`
(and hence `parameters_nonempty`), manuscript label `E:driver-parameters`.

Wrong variant: the hypothesis `Homog d alpha a` with its threshold conjunct
`a + α < 2` (`E:threshold`) dropped. At `d = 3`, `α = 2`, `a = 1/2` all other conjuncts
hold, but the `γ`-interval `0 < γ < min(1/2, (2-α)/2) = min(1/2, 0)` is empty. The
contrast theorem shows that every other conjunct of `DriverParameters.Homog` holds at
this point and that `Homog 3 2 (1/2)` itself fails, using the package theorem.

This is strictly more faithful than the earlier version, which only stated the empty
interval at `α = 2`; that emptiness is the core of the proof.

Expected outcome: compiles (refuted).
-/

namespace Refutations.DriverParameters

open StratonovichHAMSecondMoment.DriverParameters

/-- At `α = 2` the `γ`-interval of the package theorem is empty. -/
theorem gamma_empty_at_alpha_two :
    ¬ ∃ γ : ℝ, 0 < γ ∧ γ < min (1 / 2 : ℝ) ((2 - 2) / 2) := by
  rintro ⟨γ, h1, h2⟩
  have := min_le_right (1 / 2 : ℝ) ((2 - 2) / 2)
  linarith

/-- `gamma_interval_nonempty` with the threshold `a + α < 2` dropped from `Homog` is
false. -/
theorem gamma_threshold_dropped :
    ¬ (∀ (d : ℕ) (alpha a : ℝ),
      ((d = 1 ∨ d = 2 ∨ d = 3) ∧ 0 < a ∧ a < 1 ∧
        ((0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1))) →
      ∃ γ : ℝ, 0 < γ ∧ γ < min (1 / 2) ((2 - alpha) / 2)) := by
  intro h
  exact gamma_empty_at_alpha_two
    (h 3 2 (1 / 2) ⟨Or.inr (Or.inr rfl), by norm_num, by norm_num,
      Or.inl ⟨by norm_num, by norm_num⟩⟩)

/-- Contrast: at `d = 3`, `α = 2`, `a = 1/2` every conjunct of `Homog` except
`a + α < 2` holds, and `Homog 3 2 (1/2)` fails, by the package theorem
`gamma_interval_nonempty`. -/
theorem gamma_threshold_dropped_contrast :
    ((3 : ℕ) = 1 ∨ (3 : ℕ) = 2 ∨ (3 : ℕ) = 3) ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
      ((0 < (2 : ℝ) ∧ (2 : ℝ) < ((3 : ℕ) : ℝ)) ∨ ((2 : ℝ) = ((3 : ℕ) : ℝ) ∧ (3 : ℕ) = 1)) ∧
      ¬ Homog 3 2 (1 / 2) :=
  ⟨Or.inr (Or.inr rfl), by norm_num, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩,
    fun hH => gamma_empty_at_alpha_two
      (StratonovichHAMSecondMoment.DriverParameters.gamma_interval_nonempty 3 2 (1 / 2) hH)⟩

end Refutations.DriverParameters
