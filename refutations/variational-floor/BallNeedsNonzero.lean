/-
Refutation for (F2) of wave L6, package theorem
`StratonovichHAMSecondMoment.VariationalFloor.measure_ball_pos`
(`Γ(B_r) > 0`; the exhaustion-and-scaling argument of
`L:spatial-static-controls`, `notes/integrated_spatial_occupation.tex`
lines 89-91 at a284420).

Wrong variant: the hypothesis `Γ ≠ 0` dropped.  Counterexample: `Γ = 0`,
which has the set scaling of `H:homog` for every `α` (zero covariance is
admitted by `H:homog` by design).  `ball_contrast` is the package theorem
for Lebesgue measure on `ℝ¹` (set scaling with `α = 0`).  No junk-value
reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalFloor

set_option autoImplicit false

open MeasureTheory Metric
open StratonovichHAMSecondMoment HomogHypothesis VariationalDilation

namespace Refutations.VariationalFloor

/-- Without `Γ ≠ 0` the unit ball can be null. -/
theorem ball_needs_nonzero_refuted :
    ¬ (∀ (alpha : ℝ) (Γ : Measure (Rd 1)), SetScaling alpha Γ →
        0 < Γ (ball (0 : Rd 1) 1)) := by
  intro h
  have := h 0 0 (fun A _ c _ => by simp)
  simp at this

/-- Lebesgue measure on `ℝ¹` has the set scaling with `α = 0`. -/
theorem leb_scaling : SetScaling (d := 1) 0 volume := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc, sub_zero,
    Nat.cast_one, Real.rpow_one]

/-- The package theorem for Lebesgue measure: the unit ball is not null. -/
theorem ball_contrast : 0 < (volume : Measure (Rd 1)) (ball 0 1) :=
  StratonovichHAMSecondMoment.VariationalFloor.measure_ball_pos leb_scaling
    (NeZero.ne volume) one_pos

end Refutations.VariationalFloor
