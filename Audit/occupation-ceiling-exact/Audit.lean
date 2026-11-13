module
import StratonovichHAMSecondMoment.OccupationCeilingExact
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.trap
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.trap
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.trap_continuous
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.trap_continuous
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.trap_mem
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.trap_mem
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.trap_eq_zero
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.trap_eq_zero
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.trap_hasCompactSupport
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.trap_hasCompactSupport
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.trap_tendsto
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.trap_tendsto
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.idx
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.idx
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.idx_measurable
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.idx_measurable
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.idx_close
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.idx_close
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.idx_eq_iff
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.idx_eq_iff
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.ae_offNode
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.ae_offNode
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.cellInd
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.cellInd
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.sum_cellInd
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.sum_cellInd
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.stepG
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.stepG
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.stepDG
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.stepDG
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.gradSqE_grad
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.gradSqE_grad
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.stepField_isOcc
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.stepField_isOcc
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.mean_pair_bound
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.mean_pair_bound
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.step_mean_le_sqrt
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.step_mean_le_sqrt
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.occupation_rayleigh_selection_paper
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.occupation_rayleigh_selection_paper
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.A_le_Cocc
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.A_le_Cocc
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.integratedRate_sq_le_Cocc
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.integratedRate_sq_le_Cocc
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.score_le_ceiling_Cocc
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.score_le_ceiling_Cocc
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.intrinsic_occupation_ceiling_paper
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.intrinsic_occupation_ceiling_paper
#check @StratonovichHAMSecondMoment.OccupationCeilingExact.intrinsic_spatial_comparison_paper
#print axioms StratonovichHAMSecondMoment.OccupationCeilingExact.intrinsic_spatial_comparison_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.OccupationCeilingExact

open StratonovichHAMSecondMoment.OccupationCeilingExact

/-- Consumer of the wrappers: under `H:homog` and `Γ ≠ 0`, `S_1^pos ≤ U_1[C_occ]`, and
`S_2^pos < 2^m F_a(𝓔_{1/2}^𝒪)`. -/
private theorem audit_consumer {d : ℕ} {alpha a : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) :
    sSup (VariationalRate.scoreSet a Γ 1) ≤
        SpatialBracket.ceilingValue alpha 1 (RawOccupationEnergy.Cocc a alpha Γ) ∧
      sSup (VariationalRate.scoreSet a Γ 2) <
        2 ^ ((4 - alpha) / (3 - alpha)) *
          SpatialBracket.Fb alpha a (RawOccupationEnergy.EO a Γ (1 / 2)) := by
  obtain ⟨-, -, -, h1, -⟩ := intrinsic_occupation_ceiling_paper h hΓ 1 one_pos
  obtain ⟨-, -, h2, h3⟩ := intrinsic_spatial_comparison_paper h hΓ
  exact ⟨h1, lt_of_le_of_lt h2 h3⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.OccupationCeilingExact
