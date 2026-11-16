module
import StratonovichHAMSecondMoment.WhiteMomentBounds
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.WhiteSpatialEnergy
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.WhiteSpatialEnergy
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.whiteCov_ne_zero
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.whiteCov_ne_zero
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.whiteCov_zero
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.whiteCov_zero
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.F0_mono
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.F0_mono
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.ceilingValue_mono
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.ceilingValue_mono
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.white_moment_lower_of_ge
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.white_moment_lower_of_ge
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.white_moment_upper_of_le
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.white_moment_upper_of_le
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.white_moment_bounds_paper
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.white_moment_bounds_paper
#check @StratonovichHAMSecondMoment.WhiteMomentBounds.white_moment_upper_exact_paper
#print axioms StratonovichHAMSecondMoment.WhiteMomentBounds.white_moment_upper_exact_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.WhiteMomentBounds

open StratonovichHAMSecondMoment.WhiteMomentBounds

/-- Consumer of the wrapper: on the named input, the white bracket for `S_2^pos` is
nondegenerate (`0 < lower ≤ upper`). -/
private theorem audit_consumer {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1)
    (hE : WhiteSpatialEnergy c) :
    0 < WhiteRelativeWidth.lowerFormula c a ∧
      WhiteRelativeWidth.lowerFormula c a ≤ WhiteRelativeWidth.upperFormula c a := by
  obtain ⟨-, hlo, hup, -, -, hp, -⟩ := white_moment_bounds_paper hc ha0 ha1 hE
  exact ⟨hp, hlo.trans hup⟩

#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.WhiteMomentBounds
