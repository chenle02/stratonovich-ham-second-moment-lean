module

import StratonovichHAMSecondMoment.DampedNormsHomog

set_option autoImplicit false
set_option pp.all true

#check @StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass
#check @StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass.mass
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass.mass
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N0
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N0
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N1on
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N1on
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N1tail
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N1tail
#check @StratonovichHAMSecondMoment.DampedNormsHomog.KS
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.KS
#check @StratonovichHAMSecondMoment.DampedNormsHomog.KM
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.KM
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2onOuter
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2onOuter
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2onIntegrand
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2onIntegrand
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2onSq
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2onSq
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2tailSq
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2tailSq
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2tail
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2tail
#check @StratonovichHAMSecondMoment.DampedNormsHomog.smoothed
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.smoothed
#check @StratonovichHAMSecondMoment.DampedNormsHomog.FKS
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.FKS
#check @StratonovichHAMSecondMoment.DampedNormsHomog.alpha_pos
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.alpha_pos
#check @StratonovichHAMSecondMoment.DampedNormsHomog.KS_nonneg
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.KS_nonneg
#check @StratonovichHAMSecondMoment.DampedNormsHomog.KS_le
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.KS_le
#check @StratonovichHAMSecondMoment.DampedNormsHomog.KS_univ
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.KS_univ
#check @StratonovichHAMSecondMoment.DampedNormsHomog.tail_tendsto_zero
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.tail_tendsto_zero
#check @StratonovichHAMSecondMoment.DampedNormsHomog.KM_tendsto
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.KM_tendsto
#check @StratonovichHAMSecondMoment.DampedNormsHomog.weight_scaling
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.weight_scaling
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2sq_scaling
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2sq_scaling
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N1_scaling
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N1_scaling
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N0_eq
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N0_eq
#check @StratonovichHAMSecondMoment.DampedNormsHomog.FKS_integrable
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.FKS_integrable
#check @StratonovichHAMSecondMoment.DampedNormsHomog.FKS_apply
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.FKS_apply
#check @StratonovichHAMSecondMoment.DampedNormsHomog.integral_FKS_eq
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.integral_FKS_eq
#check @StratonovichHAMSecondMoment.DampedNormsHomog.inner_FKS_eq
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.inner_FKS_eq
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2onSq_eq
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2onSq_eq
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2onSq_univ
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2onSq_univ
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N1on_univ
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N1on_univ
#check @StratonovichHAMSecondMoment.DampedNormsHomog.smoothed_sFinite
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.smoothed_sFinite
#check @StratonovichHAMSecondMoment.DampedNormsHomog.integrable_mul_of_le_one
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.integrable_mul_of_le_one
#check @StratonovichHAMSecondMoment.DampedNormsHomog.smoothed_hR
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.smoothed_hR
#check @StratonovichHAMSecondMoment.DampedNormsHomog.smoothed_zero
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.smoothed_zero
#check @StratonovichHAMSecondMoment.DampedNormsHomog.resolvent_smoothed_le
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.resolvent_smoothed_le
#check @StratonovichHAMSecondMoment.DampedNormsHomog.weight_smoothed_le
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.weight_smoothed_le
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2onSq_smoothed_mono
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2onSq_smoothed_mono
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N1on_smoothed_mono
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N1on_smoothed_mono
#check @StratonovichHAMSecondMoment.DampedNormsHomog.homog_spectral_facts
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.homog_spectral_facts
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2tail_props
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2tail_props
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N1tail_tendsto
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N1tail_tendsto
#check @StratonovichHAMSecondMoment.DampedNormsHomog.N2tail_tendsto
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.N2tail_tendsto
#check @StratonovichHAMSecondMoment.DampedNormsHomog.damped_homogeneous_norms_paper
#print axioms StratonovichHAMSecondMoment.DampedNormsHomog.damped_homogeneous_norms_paper

open MeasureTheory Filter StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.DampedNormsHomog

open StratonovichHAMSecondMoment.DampedNormsHomog

/-- Consumer of the wrapper: under `H:homog` and the mass identity, `N₀(1) = 1`,
`N₂(2)² = 2^{-β} N₂(1)²`, and the printed tail `N₂^{(M)}(1)` tends to `0`. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    (G : ℝ → Measure (HomogHypothesis.Rd d)) (hG : GreenMass G) :
    N0 G 1 = 1 ∧
      DampedNorms.N2sq alpha0 2 μ = 2 ^ (-(4 - alpha - alpha0)) * DampedNorms.N2sq alpha0 1 μ ∧
      Tendsto (fun M => N2tail alpha0 M μ) atTop (nhds 0) := by
  obtain ⟨h1, -, -, -, h5, -⟩ := damped_homogeneous_norms_paper h G hG
  refine ⟨?_, (h1 2 two_pos).2.2.2.2.2, h5⟩
  rw [(h1 1 one_pos).2.2.2.1, Real.one_rpow]

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.DampedNormsHomog
