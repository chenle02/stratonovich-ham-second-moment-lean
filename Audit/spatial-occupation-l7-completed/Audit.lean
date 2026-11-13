module
import StratonovichHAMSecondMoment.SpatialOccupationL7Completed
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.squareBound_of_smooth_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.squareBound_of_smooth_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.C4_square_CS_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.C4_square_CS_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.square_pairing_CS_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.square_pairing_CS_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_homogeneous_bound_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_homogeneous_bound_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_square_CS_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_square_CS_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_four_linear_bound_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_four_linear_bound_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_four_linear_multilinear_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_four_linear_multilinear_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_four_linear_continuous_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_four_linear_continuous_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_ratio_H1_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_ratio_H1_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_four_linear_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_four_linear_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.squarePairingBounds_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.squarePairingBounds_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_energy_value_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_energy_value_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_static_energy_score_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_static_energy_score_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_static_energy_score_sSup_paper_completed
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.spatial_static_energy_score_sSup_paper_completed
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.squarePairingBounds_holds
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.squarePairingBounds_holds
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.occupation_physical_class_completed_paper
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.occupation_physical_class_completed_paper
#check @StratonovichHAMSecondMoment.SpatialOccupationL7Completed.occupation_physical_class_Esp_paper
#print axioms StratonovichHAMSecondMoment.SpatialOccupationL7Completed.occupation_physical_class_Esp_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.SpatialOccupationL7Completed

open StratonovichHAMSecondMoment.SpatialOccupationL7Completed

/-- Consumer of the wrappers: under `H:homog` and `Γ ≠ 0` alone, the original
`OccupationPhysicalClass.occupation_physical_class_paper` applies with its
`SquarePairingBounds Γ α R_0` input supplied by `squarePairingBounds_holds`, and the
occupation energy is bounded by `R_⋆^{2/(2-α)} 𝓔_sp` with `𝓔_sp > 0`. -/
private theorem audit_consumer {d : ℕ} {alpha a : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) :
    0 < OccupationPhysicalClass.EstarO a ((4 - alpha) - 2 * a) Γ ∧
      OccupationPhysicalClass.EstarO a ((4 - alpha) - 2 * a) Γ ≤
        OccupationKernelRow.Rstar a ((4 - alpha) - 2 * a) ^ (2 / (2 - alpha)) *
          SpatialFourLinear.Esp Γ ∧
      OccupationPhysicalClass.EstarO a ((4 - alpha) - 2 * a) Γ ≤
        OccupationKernelRow.Rstar a ((4 - alpha) - 2 * a) ^ (2 / (2 - alpha)) *
          OccupationPhysicalClass.spEnergyVal alpha (SpatialSmoothRatio.R0 Γ alpha) :=
  ⟨(occupation_physical_class_Esp_paper hH hΓ _ rfl).2.2.2.1,
    (occupation_physical_class_Esp_paper hH hΓ _ rfl).2.2.2.2.1,
    (OccupationPhysicalClass.occupation_physical_class_paper hH hΓ _ rfl
      (squarePairingBounds_holds hH hΓ)).2.2.2.2⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.SpatialOccupationL7Completed
