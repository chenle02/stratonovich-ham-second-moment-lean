module
import StratonovichHAMSecondMoment.PhaseShiftControl
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.PhaseShiftControl.weight_le
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.weight_le
#check @StratonovichHAMSecondMoment.PhaseShiftControl.lintegral_average_le
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.lintegral_average_le
#check @StratonovichHAMSecondMoment.PhaseShiftControl.integral_gauss_volume
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.integral_gauss_volume
#check @StratonovichHAMSecondMoment.PhaseShiftControl.integrable_gauss_volume
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.integrable_gauss_volume
#check @StratonovichHAMSecondMoment.PhaseShiftControl.lintegral_gauss_volume
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.lintegral_gauss_volume
#check @StratonovichHAMSecondMoment.PhaseShiftControl.integral_gauss_homog
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.integral_gauss_homog
#check @StratonovichHAMSecondMoment.PhaseShiftControl.not_gauss_shift_invariant
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.not_gauss_shift_invariant
#check @StratonovichHAMSecondMoment.PhaseShiftControl.not_gauss_shift_invariant_phase
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.not_gauss_shift_invariant_phase
#check @StratonovichHAMSecondMoment.PhaseShiftControl.exists_gauss_shift_lt_phase
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.exists_gauss_shift_lt_phase
#check @StratonovichHAMSecondMoment.PhaseShiftControl.phaseCovariance_zero
#print axioms StratonovichHAMSecondMoment.PhaseShiftControl.phaseCovariance_zero

open MeasureTheory StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.PhaseContractions
open StratonovichHAMSecondMoment.PhaseShiftControl

namespace StratonovichHAMSecondMoment.Audit.PhaseShiftControl

/-- Consumer: under `H:homog` in `d = 3` with `μ ≠ 0`, the shifted Gaussian
masses are not all equal, and the pairing inequality is strict at a nonzero
shift. -/
private theorem audit_consumer {alpha alpha0 : ℝ} {Γ μ : Measure (Rd 3)}
    (h : HomogCovariance 3 alpha alpha0 Γ μ) (hμ : μ ≠ 0) :
    (¬ ∀ q : Rd 3, ∫ ξ, Real.exp (-(1 * ‖q + ξ‖ ^ 2)) ∂μ =
      ∫ ξ, Real.exp (-(1 * ‖ξ‖ ^ 2)) ∂μ) ∧
    ∃ q : Rd 3, q ≠ 0 ∧ ∫ ξ, Real.exp (-(1 * ‖q + ξ‖ ^ 2)) ∂μ <
      ∫ ξ, Real.exp (-(1 * ‖ξ‖ ^ 2)) ∂μ :=
  ⟨not_gauss_shift_invariant_phase (PhaseCovariance.of_homog h) hμ one_pos,
    exists_gauss_shift_lt_phase (PhaseCovariance.of_homog h) hμ one_pos⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.PhaseShiftControl
