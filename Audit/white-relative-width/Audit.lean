module
import StratonovichHAMSecondMoment.WhiteRelativeWidth
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.boundMass
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.boundMass
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.lowerFormula
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.lowerFormula
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.upperFormula
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.upperFormula
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.widthConst
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.widthConst
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_pos
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_pos
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.boundMass_pos
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.boundMass_pos
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.boundMass_eq_mass
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.boundMass_eq_mass
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.gamma_one_add_dup
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.gamma_one_add_dup
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.gamma_three_sub_rec
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.gamma_three_sub_rec
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_mul_boundMass
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_mul_boundMass
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.gamma_mid_sq_le
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.gamma_mid_sq_le
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.gamma_five_quarters_sq_le
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.gamma_five_quarters_sq_le
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_mul_boundMass_le
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_mul_boundMass_le
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.relative_width_le
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.relative_width_le
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.relative_width_eq_half
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.relative_width_eq_half
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_mul_boundMass_symm
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_mul_boundMass_symm
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.ratio_eq
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.ratio_eq
#check @StratonovichHAMSecondMoment.WhiteRelativeWidth.white_relative_width_paper
#print axioms StratonovichHAMSecondMoment.WhiteRelativeWidth.white_relative_width_paper

open StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.WhiteRelativeWidth

open StratonovichHAMSecondMoment.WhiteRelativeWidth

/-- Consumer of the wrapper: for `c > 0` and `0 < a < 1` the ratio of the upper to
the lower formula is at most `[sqrt π/(2 Γ_E(5/4)²)]^{1/2}`, and the displayed `M_a`
is the temporal-equilibrium mass. -/
private theorem audit_consumer {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1) :
    upperFormula c a / lowerFormula c a ≤ Real.sqrt (Real.sqrt Real.pi / (2 * Real.Gamma (5 / 4) ^ 2)) ∧
      boundMass a = TemporalEquilibrium.mass a := by
  obtain ⟨h1, h2, -⟩ := white_relative_width_paper hc ha0 ha1
  exact ⟨h1 ▸ h2, boundMass_eq_mass ha0 ha1⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.WhiteRelativeWidth
