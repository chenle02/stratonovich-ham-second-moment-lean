-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path or universe order, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFeatures
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real
open HomogHypothesis (Rd HomogCovariance)
open WickInterface (kerA capSet capSet_max capSet_of_pos measurableSet_capSet capSet_subset_Ioi)
open PairingInterface (nuE)
open LowAlphaConvolution (gammaEps gaussFactor gammaEps_spectral integrable_gaussFactor gaussFactor_pos gaussFactor_le_one)
open SourceInterface
variable {d : ℕ}
/-- Under hH : HomogCovariance d alpha alpha0 Gamma mu, for delta > 0 and all delta', s, s': temp delta s * temp delta' s' is integrable for nuBase alpha0 x Lebesgue and its integral is (kerA alpha0 (capSet (max delta delta')) (s - s')).toReal. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFeatures.temp_gram {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    {δ : ℝ} (hδ : 0 < δ) (δ' s s' : ℝ) :
    Integrable (fun z => temp δ s z * temp δ' s' z) ((nuBase α₀).prod volume) ∧
      ∫ z, temp δ s z * temp δ' s' z ∂(nuBase α₀).prod volume =
        (kerA α₀ (capSet (max δ δ')) (s - s')).toReal := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFeatures
