module
import StratonovichHAMSecondMoment.L8Completed
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.L8Completed.K0_eq
#print axioms StratonovichHAMSecondMoment.L8Completed.K0_eq
#check @StratonovichHAMSecondMoment.L8Completed.ceilingValue_eq
#print axioms StratonovichHAMSecondMoment.L8Completed.ceilingValue_eq
#check @StratonovichHAMSecondMoment.L8Completed.spaceTimeCS_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.spaceTimeCS_completed
#check @StratonovichHAMSecondMoment.L8Completed.occupation_ceiling_K0_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.occupation_ceiling_K0_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.s1Bdd_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.s1Bdd_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.occupation_ceiling_sSup_K0_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.occupation_ceiling_sSup_K0_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.variational_positive_scores_sSup_st_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.variational_positive_scores_sSup_st_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.spatial_static_score_sSup_st_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.spatial_static_score_sSup_st_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.spatial_smooth_score_sSup_st_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.spatial_smooth_score_sSup_st_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.R0_le_of_st_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.R0_le_of_st_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.spatial_static_energy_score_sSup_st_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.spatial_static_energy_score_sSup_st_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.occupationCeilingK0_holds
#print axioms StratonovichHAMSecondMoment.L8Completed.occupationCeilingK0_holds
#check @StratonovichHAMSecondMoment.L8Completed.spatial_bracket_lower_sSup_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.spatial_bracket_lower_sSup_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.spatial_bracket_upper_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.spatial_bracket_upper_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.intrinsic_spatial_bracket_paper_completed
#print axioms StratonovichHAMSecondMoment.L8Completed.intrinsic_spatial_bracket_paper_completed
#check @StratonovichHAMSecondMoment.L8Completed.uniform_series_tail_terminal_wick_paper
#print axioms StratonovichHAMSecondMoment.L8Completed.uniform_series_tail_terminal_wick_paper
#check @StratonovichHAMSecondMoment.L8Completed.freeWaveData_nonempty
#print axioms StratonovichHAMSecondMoment.L8Completed.freeWaveData_nonempty

namespace StratonovichHAMSecondMoment.Audit.L8Completed

open StratonovichHAMSecondMoment

/-- Consumer: under `H:homog` and `Γ ≠ 0` alone, `S1Bdd` holds and `S_2^pos` lies in the
bracket `2^m M_a^{-1/k} F₀(𝓔_sp) ≤ S_2^pos ≤ 2^m K_0^{1/k} F₀(𝓔_sp)`. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    VariationalRate.S1Bdd alpha0 Γ ∧
      2 ^ ((4 - alpha) / (3 - alpha)) * (TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) *
          SpatialFourLinear.F0 alpha (SpatialFourLinear.Esp Γ)) ≤
        sSup (VariationalRate.scoreSet alpha0 Γ 2) ∧
      sSup (VariationalRate.scoreSet alpha0 Γ 2) ≤
        2 ^ ((4 - alpha) / (3 - alpha)) * SpatialBracket.K0 alpha0 ^ (1 / (3 - alpha)) *
          SpatialFourLinear.F0 alpha (SpatialFourLinear.Esp Γ) :=
  ⟨L8Completed.s1Bdd_paper_completed hH hΓ,
    L8Completed.spatial_bracket_lower_sSup_paper_completed hH hΓ,
    (L8Completed.spatial_bracket_upper_paper_completed hH hΓ).2⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.L8Completed
