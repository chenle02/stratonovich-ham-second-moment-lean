module
import StratonovichHAMSecondMoment.SpatialBracket
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.SpatialBracket.K0
#print axioms StratonovichHAMSecondMoment.SpatialBracket.K0
#check @StratonovichHAMSecondMoment.SpatialBracket.coef
#print axioms StratonovichHAMSecondMoment.SpatialBracket.coef
#check @StratonovichHAMSecondMoment.SpatialBracket.Fb
#print axioms StratonovichHAMSecondMoment.SpatialBracket.Fb
#check @StratonovichHAMSecondMoment.SpatialBracket.logGap
#print axioms StratonovichHAMSecondMoment.SpatialBracket.logGap
#check @StratonovichHAMSecondMoment.SpatialBracket.Dzeta
#print axioms StratonovichHAMSecondMoment.SpatialBracket.Dzeta
#check @StratonovichHAMSecondMoment.SpatialBracket.ceilingValue
#print axioms StratonovichHAMSecondMoment.SpatialBracket.ceilingValue
#check @StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0
#print axioms StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0
#check @StratonovichHAMSecondMoment.SpatialBracket.K0_pos
#print axioms StratonovichHAMSecondMoment.SpatialBracket.K0_pos
#check @StratonovichHAMSecondMoment.SpatialBracket.coef_pos
#print axioms StratonovichHAMSecondMoment.SpatialBracket.coef_pos
#check @StratonovichHAMSecondMoment.SpatialBracket.Fb_zero
#print axioms StratonovichHAMSecondMoment.SpatialBracket.Fb_zero
#check @StratonovichHAMSecondMoment.SpatialBracket.Fb_pos
#print axioms StratonovichHAMSecondMoment.SpatialBracket.Fb_pos
#check @StratonovichHAMSecondMoment.SpatialBracket.Fb_zero_eq_F0
#print axioms StratonovichHAMSecondMoment.SpatialBracket.Fb_zero_eq_F0
#check @StratonovichHAMSecondMoment.SpatialBracket.log_coef
#print axioms StratonovichHAMSecondMoment.SpatialBracket.log_coef
#check @StratonovichHAMSecondMoment.SpatialBracket.logGap_pos
#print axioms StratonovichHAMSecondMoment.SpatialBracket.logGap_pos
#check @StratonovichHAMSecondMoment.SpatialBracket.log_Fb_ratio
#print axioms StratonovichHAMSecondMoment.SpatialBracket.log_Fb_ratio
#check @StratonovichHAMSecondMoment.SpatialBracket.F0_lt_Fa
#print axioms StratonovichHAMSecondMoment.SpatialBracket.F0_lt_Fa
#check @StratonovichHAMSecondMoment.SpatialBracket.F0_mul
#print axioms StratonovichHAMSecondMoment.SpatialBracket.F0_mul
#check @StratonovichHAMSecondMoment.SpatialBracket.energyValue_pow
#print axioms StratonovichHAMSecondMoment.SpatialBracket.energyValue_pow
#check @StratonovichHAMSecondMoment.SpatialBracket.ceilingValue_eq_half
#print axioms StratonovichHAMSecondMoment.SpatialBracket.ceilingValue_eq_half
#check @StratonovichHAMSecondMoment.SpatialBracket.Dzeta_half
#print axioms StratonovichHAMSecondMoment.SpatialBracket.Dzeta_half
#check @StratonovichHAMSecondMoment.SpatialBracket.ceilingValue_mul
#print axioms StratonovichHAMSecondMoment.SpatialBracket.ceilingValue_mul
#check @StratonovichHAMSecondMoment.SpatialBracket.ceilingValue_eq_zeta
#print axioms StratonovichHAMSecondMoment.SpatialBracket.ceilingValue_eq_zeta
#check @StratonovichHAMSecondMoment.SpatialBracket.ceiling_ratio_exp
#print axioms StratonovichHAMSecondMoment.SpatialBracket.ceiling_ratio_exp
#check @StratonovichHAMSecondMoment.SpatialBracket.counterexample_integers
#print axioms StratonovichHAMSecondMoment.SpatialBracket.counterexample_integers
#check @StratonovichHAMSecondMoment.SpatialBracket.counterexample_log
#print axioms StratonovichHAMSecondMoment.SpatialBracket.counterexample_log
#check @StratonovichHAMSecondMoment.SpatialBracket.counterexample_ratio
#print axioms StratonovichHAMSecondMoment.SpatialBracket.counterexample_ratio
#check @StratonovichHAMSecondMoment.SpatialBracket.S1Bdd_of_ceiling
#print axioms StratonovichHAMSecondMoment.SpatialBracket.S1Bdd_of_ceiling
#check @StratonovichHAMSecondMoment.SpatialBracket.spatial_bracket_lower_paper
#print axioms StratonovichHAMSecondMoment.SpatialBracket.spatial_bracket_lower_paper
#check @StratonovichHAMSecondMoment.SpatialBracket.spatial_bracket_lower_sSup_paper
#print axioms StratonovichHAMSecondMoment.SpatialBracket.spatial_bracket_lower_sSup_paper
#check @StratonovichHAMSecondMoment.SpatialBracket.spatial_bracket_upper_paper
#print axioms StratonovichHAMSecondMoment.SpatialBracket.spatial_bracket_upper_paper
#check @StratonovichHAMSecondMoment.SpatialBracket.intrinsic_spatial_bracket_paper
#print axioms StratonovichHAMSecondMoment.SpatialBracket.intrinsic_spatial_bracket_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.SpatialBracket

open StratonovichHAMSecondMoment.SpatialBracket

/-- Consumer of the wrapper: under `H:homog`, `Γ ≠ 0` and the named input, `S_2^pos` lies in the
bracket `[2^m M_a^{-1/k} F₀(𝓔_sp), 2^m K_0^{1/k} F₀(𝓔_sp)]`, and the lower end is at most the
upper end. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hC : OccupationCeilingK0 alpha alpha0 Γ) :
    2 ^ ((4 - alpha) / (3 - alpha)) *
        (TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) *
          SpatialFourLinear.F0 alpha (SpatialFourLinear.Esp Γ)) ≤
      2 ^ ((4 - alpha) / (3 - alpha)) * K0 alpha0 ^ (1 / (3 - alpha)) *
        SpatialFourLinear.F0 alpha (SpatialFourLinear.Esp Γ) := by
  obtain ⟨-, -, hlo, hup, -⟩ := intrinsic_spatial_bracket_paper h hΓ hC
  exact hlo.trans hup

#check @audit_consumer
#print axioms audit_consumer

example : Fb 1 0 0 = 0 := Fb_zero (by norm_num) 0

end StratonovichHAMSecondMoment.Audit.SpatialBracket
