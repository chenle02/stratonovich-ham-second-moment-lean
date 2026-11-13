module
import StratonovichHAMSecondMoment.SpectralMassIdentity
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.ralpha
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.ralpha
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.beta_real
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.beta_real
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.levelset_eq_ball
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.levelset_eq_ball
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_one_eq_ralpha
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_one_eq_ralpha
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_eq_ralpha
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_eq_ralpha
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.alpha_mem_Ioo_of_homog
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.alpha_mem_Ioo_of_homog
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_eq_ralpha_paper
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_eq_ralpha_paper
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.hRdef_iff_resolvent
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.hRdef_iff_resolvent
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.hRdef_iff_resolvent_paper
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.hRdef_iff_resolvent_paper
#check @StratonovichHAMSecondMoment.SpectralMassIdentity.spatial_fourier_bound_ralpha_paper
#print axioms StratonovichHAMSecondMoment.SpectralMassIdentity.spatial_fourier_bound_ralpha_paper
open MeasureTheory StratonovichHAMSecondMoment in
/-- Consumer: under `H:homog`, the spatial energy ratio is at most `2^{1+α} R_α`
times `b^{α/2}`, and `R_α = R_Γ(1)`. -/
theorem spatial_bound_consumer {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {g : HomogHypothesis.Rd d → ℝ} (hg : SpatialFourierBound.IsUnitTest g) :
    SpatialFourierBound.spatialEnergy Γ g ≤
        2 ^ (1 + alpha) * SpectralMassIdentity.ralpha μ alpha *
          SpatialFourierBound.gradEnergy g ^ (alpha / 2) ∧
      SpectralHomog.resolvent μ 1 = SpectralMassIdentity.ralpha μ alpha :=
  ⟨(SpectralMassIdentity.spatial_fourier_bound_ralpha_paper hH hg).2.2.2.2.2.2,
    (SpectralMassIdentity.resolvent_eq_ralpha_paper hH).1⟩
#check @spatial_bound_consumer
#print axioms spatial_bound_consumer
