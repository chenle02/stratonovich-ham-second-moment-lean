module
import StratonovichHAMSecondMoment.SpatialOccupationCompleted
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.SpatialOccupationCompleted.rayleighFloor_of_homog
#print axioms StratonovichHAMSecondMoment.SpatialOccupationCompleted.rayleighFloor_of_homog
#check @StratonovichHAMSecondMoment.SpatialOccupationCompleted.spatial_static_controls_completed_paper
#print axioms StratonovichHAMSecondMoment.SpatialOccupationCompleted.spatial_static_controls_completed_paper
#check @StratonovichHAMSecondMoment.SpatialOccupationCompleted.staticControls_of_homog
#print axioms StratonovichHAMSecondMoment.SpatialOccupationCompleted.staticControls_of_homog
#check @StratonovichHAMSecondMoment.SpatialOccupationCompleted.spatial_smooth_score_completed_paper
#print axioms StratonovichHAMSecondMoment.SpatialOccupationCompleted.spatial_smooth_score_completed_paper
#check @StratonovichHAMSecondMoment.SpatialOccupationCompleted.spatial_smooth_score_sSup_completed_paper
#print axioms StratonovichHAMSecondMoment.SpatialOccupationCompleted.spatial_smooth_score_sSup_completed_paper
#check @StratonovichHAMSecondMoment.SpatialOccupationCompleted.R0_finite_of_S1Bdd_completed_paper
#print axioms StratonovichHAMSecondMoment.SpatialOccupationCompleted.R0_finite_of_S1Bdd_completed_paper
#check @StratonovichHAMSecondMoment.SpatialOccupationCompleted.spatial_smooth_ratio_completed_paper
#print axioms StratonovichHAMSecondMoment.SpatialOccupationCompleted.spatial_smooth_ratio_completed_paper
set_option pp.all false

namespace StratonovichHAMSecondMoment.Audit.SpatialOccupationCompleted

open MeasureTheory StratonovichHAMSecondMoment SpatialOccupationCompleted

/-- Consumer of the completed wrappers: under `H:homog` and `Γ ≠ 0` alone,
`R_0` is positive and, for every nonnegative nonzero test function `z`,
`λ_z(1) > 0`. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    {z : HomogHypothesis.Rd d → ℝ} (hz : WeakSobolev.IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x)
    (hzne : z ≠ 0) :
    0 < SpatialSmoothRatio.R0 Γ alpha ∧ 0 < SpatialStaticControls.lamZ Γ z 1 :=
  ⟨(spatial_smooth_ratio_completed_paper h hΓ).1.2.2.1,
    ((spatial_static_controls_completed_paper h hΓ hz hz0 hzne).2.1 1 one_pos).2.2.2.1⟩

end StratonovichHAMSecondMoment.Audit.SpatialOccupationCompleted
