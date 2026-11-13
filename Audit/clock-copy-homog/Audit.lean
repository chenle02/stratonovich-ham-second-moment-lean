module
import StratonovichHAMSecondMoment.ClockCopyHomog
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.ClockCopyHomog.clock_copy_obstruction_paper
#print axioms StratonovichHAMSecondMoment.ClockCopyHomog.clock_copy_obstruction_paper
#check @StratonovichHAMSecondMoment.ClockCopyHomog.damped_N2_nonneg_paper
#print axioms StratonovichHAMSecondMoment.ClockCopyHomog.damped_N2_nonneg_paper
#check @StratonovichHAMSecondMoment.ClockCopyHomog.damped_norms_finite_paper
#print axioms StratonovichHAMSecondMoment.ClockCopyHomog.damped_norms_finite_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.ClockCopyHomog

open StratonovichHAMSecondMoment.ClockCopyHomog

/-- Consumer of the wrapper: under `H:homog` and `Γ ≠ 0`, the clock-copy
candidate falls strictly short of `K_Γ(θ)`, with no supplied input. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    ClockCopy.J alpha0 1 μ 1 < DampedNorms.N2sq alpha0 1 μ :=
  (clock_copy_obstruction_paper h hΓ 1 one_pos 1 ⟨by norm_num, le_rfl⟩).2.2.2.2.2.2.2.2.2.2.1

#check @audit_consumer
#print axioms audit_consumer

example {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) :
    0 ≤ DampedNorms.N2sq alpha0 1 μ :=
  damped_N2_nonneg_paper h 1 one_pos

end StratonovichHAMSecondMoment.Audit.ClockCopyHomog
