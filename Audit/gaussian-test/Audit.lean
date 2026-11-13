module
import StratonovichHAMSecondMoment.GaussianTest
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.GaussianTest.poly_mul_exp_neg_sq_le
#print axioms StratonovichHAMSecondMoment.GaussianTest.poly_mul_exp_neg_sq_le
#check @StratonovichHAMSecondMoment.GaussianTest.gauss
#print axioms StratonovichHAMSecondMoment.GaussianTest.gauss
#check @StratonovichHAMSecondMoment.GaussianTest.contDiff_gauss
#print axioms StratonovichHAMSecondMoment.GaussianTest.contDiff_gauss
#check @StratonovichHAMSecondMoment.GaussianTest.norm_iteratedFDeriv_exp_le
#print axioms StratonovichHAMSecondMoment.GaussianTest.norm_iteratedFDeriv_exp_le
#check @StratonovichHAMSecondMoment.GaussianTest.gauss_decay
#print axioms StratonovichHAMSecondMoment.GaussianTest.gauss_decay
#check @StratonovichHAMSecondMoment.GaussianTest.gaussSchwartz
#print axioms StratonovichHAMSecondMoment.GaussianTest.gaussSchwartz
#check @StratonovichHAMSecondMoment.GaussianTest.gaussSchwartz_apply
#print axioms StratonovichHAMSecondMoment.GaussianTest.gaussSchwartz_apply
#check @StratonovichHAMSecondMoment.GaussianTest.phase_hasTemperateGrowth
#print axioms StratonovichHAMSecondMoment.GaussianTest.phase_hasTemperateGrowth
#check @StratonovichHAMSecondMoment.GaussianTest.sub_hasTemperateGrowth
#print axioms StratonovichHAMSecondMoment.GaussianTest.sub_hasTemperateGrowth
#check @StratonovichHAMSecondMoment.GaussianTest.sub_upper
#print axioms StratonovichHAMSecondMoment.GaussianTest.sub_upper
#check @StratonovichHAMSecondMoment.GaussianTest.gaussTest
#print axioms StratonovichHAMSecondMoment.GaussianTest.gaussTest
#check @StratonovichHAMSecondMoment.GaussianTest.gaussTest_apply
#print axioms StratonovichHAMSecondMoment.GaussianTest.gaussTest_apply
#check @StratonovichHAMSecondMoment.GaussianTest.gaussTest_fourier
#print axioms StratonovichHAMSecondMoment.GaussianTest.gaussTest_fourier

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.GaussianTest

open StratonovichHAMSecondMoment.GaussianTest

/-- Consumer: the Gaussian test is integrable and its value at the centre. -/
private theorem audit_consumer (d : ℕ) :
    Integrable (fun x => gaussTest (E := HomogHypothesis.Rd d) 1 one_pos 0 0 x) ∧
      gaussTest (E := HomogHypothesis.Rd d) 1 one_pos 0 0 0 = 1 := by
  refine ⟨(gaussTest 1 one_pos 0 0).integrable, ?_⟩
  rw [gaussTest_apply]; simp

#check @audit_consumer
#print axioms audit_consumer

example : gaussSchwartz (E := ℝ) 1 one_pos 0 = 1 := by simp

end StratonovichHAMSecondMoment.Audit.GaussianTest
