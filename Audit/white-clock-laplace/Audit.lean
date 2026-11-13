module
import StratonovichHAMSecondMoment.WhiteClockLaplace
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.laplace_id
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.laplace_id
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.laplace_rpow
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.laplace_rpow
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.volume_restrict_quadrant
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.volume_restrict_quadrant
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.quadrant_mul
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.quadrant_mul
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.quadrant_iterated
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.quadrant_iterated
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.crossIntegrand
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.crossIntegrand
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.crossValue
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.crossValue
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.upperHalf
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.upperHalf
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.lowerHalf
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.lowerHalf
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.measurableSet_upperHalf
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.measurableSet_upperHalf
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.measurableSet_lowerHalf
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.measurableSet_lowerHalf
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.crossIntegrand_swap
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.crossIntegrand_swap
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.shear_measurePreserving
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.shear_measurePreserving
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.shear_measurableEmbedding
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.shear_measurableEmbedding
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.swap_measurableEmbedding
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.swap_measurableEmbedding
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.shear_preimage_upperHalf
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.shear_preimage_upperHalf
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.crossIntegrand_shear
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.crossIntegrand_shear
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.cross_upperHalf
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.cross_upperHalf
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.cross_lowerHalf
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.cross_lowerHalf
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.crossIntegrand_split
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.crossIntegrand_split
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.cross_transform
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.cross_transform
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.cross_transform_iterated
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.cross_transform_iterated
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.crossValue_diag
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.crossValue_diag
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.selfIntegrand
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.selfIntegrand
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.selfValue
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.selfValue
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.self_transform
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.self_transform
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.green
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.green
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.green_cross_factor
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.green_cross_factor
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.green_self_factor
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.green_self_factor
#check @StratonovichHAMSecondMoment.WhiteClockLaplace.white_clock_laplace_paper
#print axioms StratonovichHAMSecondMoment.WhiteClockLaplace.white_clock_laplace_paper

open MeasureTheory Set

namespace StratonovichHAMSecondMoment.Audit.WhiteClockLaplace

open StratonovichHAMSecondMoment.WhiteClockLaplace

/-- Consumer of the wrapper: on the diagonal `θ₁ = θ₂ = η₁ = η₂ = θ` the cross
transform is half the self transform (`Γ_E(1-a)/(4θ^{3-a})` against
`Γ_E(1-a)/(2θ^{3-a})`), both integrals being genuine (integrable integrands). -/
private theorem audit_consumer {a θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    IntegrableOn (crossIntegrand a θ θ) (Ioi 0 ×ˢ Ioi 0) ∧
      IntegrableOn (selfIntegrand a θ θ) (Ioi 0 ×ˢ Ioi 0) ∧
      2 * ∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ),
          Real.exp (-θ * s - θ * t) * |s - t| ^ (-a) * (min s t / 2) =
        ∫ r₂ in Ioi (0:ℝ), ∫ r₁ in Ioi (0:ℝ),
          Real.exp (-θ * r₁ - θ * r₂) * r₂ ^ (-a) * (r₁ / 2) := by
  obtain ⟨-, hD, hS⟩ := white_clock_laplace_paper ha0 ha1 hθ hθ hθ hθ
  obtain ⟨hDI, hDV⟩ := hD θ hθ
  refine ⟨hDI, hS.1, ?_⟩
  rw [hDV, hS.2]
  have h : θ ^ (1 - a) * θ ^ (2:ℕ) = θ ^ (3 - a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hθ]; norm_num; ring_nf
  have h3 : 0 < θ ^ (3 - a) := Real.rpow_pos_of_pos hθ _
  rw [← h]
  have : 0 < θ ^ (1 - a) := Real.rpow_pos_of_pos hθ _
  field_simp
  ring

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.WhiteClockLaplace
