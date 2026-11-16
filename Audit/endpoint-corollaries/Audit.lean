module
import StratonovichHAMSecondMoment.EndpointCorollaries
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.EndpointCorollaries.rieszMeasure
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.rieszMeasure
#check @StratonovichHAMSecondMoment.EndpointCorollaries.RieszIsoPD
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.RieszIsoPD
#check @StratonovichHAMSecondMoment.EndpointCorollaries.integrable_norm_rpow_mul
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.integrable_norm_rpow_mul
#check @StratonovichHAMSecondMoment.EndpointCorollaries.riesz_smul
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.riesz_smul
#check @StratonovichHAMSecondMoment.EndpointCorollaries.riesz_props
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.riesz_props
#check @StratonovichHAMSecondMoment.EndpointCorollaries.riesz_comparison
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.riesz_comparison
#check @StratonovichHAMSecondMoment.EndpointCorollaries.withDensity_ne_zero_of_ae_pos
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.withDensity_ne_zero_of_ae_pos
#check @StratonovichHAMSecondMoment.EndpointCorollaries.prodRieszMeasure_ne_zero
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.prodRieszMeasure_ne_zero
#check @StratonovichHAMSecondMoment.EndpointCorollaries.rieszMeasure_ne_zero
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.rieszMeasure_ne_zero
#check @StratonovichHAMSecondMoment.EndpointCorollaries.map_ne_zero_of_ne_zero
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.map_ne_zero_of_ne_zero
#check @StratonovichHAMSecondMoment.EndpointCorollaries.wsum_ne_zero
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.wsum_ne_zero
#check @StratonovichHAMSecondMoment.EndpointCorollaries.ThreeMomentModel
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.ThreeMomentModel
#check @StratonovichHAMSecondMoment.EndpointCorollaries.lowConst
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.lowConst
#check @StratonovichHAMSecondMoment.EndpointCorollaries.staticConst
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.staticConst
#check @StratonovichHAMSecondMoment.EndpointCorollaries.TransferConclusion
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.TransferConclusion
#check @StratonovichHAMSecondMoment.EndpointCorollaries.ThreeTransfer
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.ThreeTransfer
#check @StratonovichHAMSecondMoment.EndpointCorollaries.midTheta
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.midTheta
#check @StratonovichHAMSecondMoment.EndpointCorollaries.midTheta_mem
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.midTheta_mem
#check @StratonovichHAMSecondMoment.EndpointCorollaries.riesz_endpoints
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.riesz_endpoints
#check @StratonovichHAMSecondMoment.EndpointCorollaries.product_target
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.product_target
#check @StratonovichHAMSecondMoment.EndpointCorollaries.three_product_riesz_paper
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.three_product_riesz_paper
#check @StratonovichHAMSecondMoment.EndpointCorollaries.Component
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.Component
#check @StratonovichHAMSecondMoment.EndpointCorollaries.Component.Valid
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.Component.Valid
#check @StratonovichHAMSecondMoment.EndpointCorollaries.Component.meas
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.Component.meas
#check @StratonovichHAMSecondMoment.EndpointCorollaries.Component.low
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.Component.low
#check @StratonovichHAMSecondMoment.EndpointCorollaries.Component.st
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.Component.st
#check @StratonovichHAMSecondMoment.EndpointCorollaries.component_endpoints
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.component_endpoints
#check @StratonovichHAMSecondMoment.EndpointCorollaries.three_finite_images_paper
#print axioms StratonovichHAMSecondMoment.EndpointCorollaries.three_finite_images_paper
set_option pp.all false

namespace StratonovichHAMSecondMoment.Audit.EndpointCorollaries

open MeasureTheory StratonovichHAMSecondMoment.EndpointLemmas
  StratonovichHAMSecondMoment.EndpointCorollaries
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- Consumer: one isotropic Riesz component pushed by an invertible `T` with weight one; the
target satisfies `H:three-endpoints` and, with `ThreeTransfer`, the transfer conclusions. -/
theorem audit_consumer (hPD : RieszProductPD) (hIso : RieszIsoPD) (hPl : PlaneRieszPD)
    (Mdl : ThreeMomentModel) {α₀ α c : ℝ} (hT : ThreeTransfer Mdl α₀ (midTheta α₀ α))
    (hα₀ : 0 < α₀) (hα₀1 : α₀ < 1) (hα1 : 1 < α) (hα2 : α < 2 - α₀) (hc : 0 < c)
    (T : Rd 3 ≃L[ℝ] Rd 3) :
    ThreeEndpoints (midTheta α₀ α) (chi α (midTheta α₀ α))
        (wsum (fun _ : Fin 1 => (1 : ℝ)) fun _ => ((Component.riesz c).meas α).map T) ∧
      ∃ L S, TransferConclusion Mdl α₀ α (midTheta α₀ α)
        (wsum (fun _ : Fin 1 => (1 : ℝ)) fun _ => ((Component.riesz c).meas α).map T) L S := by
  obtain ⟨-, hpair, hconc⟩ := three_finite_images_paper hPD hIso hPl Mdl hT hα₀ hα₀1 hα1 hα2
    (fun _ : Fin 1 => Component.riesz c) (fun _ => hc) (fun _ => T) (fun _ => zero_le_one)
    (by simp)
  exact ⟨⟨_, _, hpair⟩, _, _, hconc⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.EndpointCorollaries
