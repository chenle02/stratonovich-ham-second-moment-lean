module
import StratonovichHAMSecondMoment.VariationalDilation
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.WeakSobolev.IsTestFunction
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsTestFunction
#check @StratonovichHAMSecondMoment.WeakSobolev.HasWeakGradient
#print axioms StratonovichHAMSecondMoment.WeakSobolev.HasWeakGradient
#check @StratonovichHAMSecondMoment.WeakSobolev.MemH1
#print axioms StratonovichHAMSecondMoment.WeakSobolev.MemH1
#check @StratonovichHAMSecondMoment.WeakSobolev.weakGradient_ae_unique
#print axioms StratonovichHAMSecondMoment.WeakSobolev.weakGradient_ae_unique
#check @StratonovichHAMSecondMoment.WeakSobolev.dilL2
#print axioms StratonovichHAMSecondMoment.WeakSobolev.dilL2
#check @StratonovichHAMSecondMoment.WeakSobolev.rpow_half_sq
#print axioms StratonovichHAMSecondMoment.WeakSobolev.rpow_half_sq
#check @StratonovichHAMSecondMoment.WeakSobolev.integral_jacobian
#print axioms StratonovichHAMSecondMoment.WeakSobolev.integral_jacobian
#check @StratonovichHAMSecondMoment.WeakSobolev.integrable_jacobian_iff
#print axioms StratonovichHAMSecondMoment.WeakSobolev.integrable_jacobian_iff
#check @StratonovichHAMSecondMoment.WeakSobolev.memLp_dilL2
#print axioms StratonovichHAMSecondMoment.WeakSobolev.memLp_dilL2
#check @StratonovichHAMSecondMoment.WeakSobolev.norm_dilL2_sq
#print axioms StratonovichHAMSecondMoment.WeakSobolev.norm_dilL2_sq
#check @StratonovichHAMSecondMoment.WeakSobolev.integral_norm_dilL2_sq
#print axioms StratonovichHAMSecondMoment.WeakSobolev.integral_norm_dilL2_sq
#check @StratonovichHAMSecondMoment.WeakSobolev.hasWeakGradient_dilL2
#print axioms StratonovichHAMSecondMoment.WeakSobolev.hasWeakGradient_dilL2
#check @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial
#check @StratonovichHAMSecondMoment.WeakSobolev.rayleighValue
#print axioms StratonovichHAMSecondMoment.WeakSobolev.rayleighValue
#check @StratonovichHAMSecondMoment.WeakSobolev.rayleighSet
#print axioms StratonovichHAMSecondMoment.WeakSobolev.rayleighSet
#check @StratonovichHAMSecondMoment.WeakSobolev.rayleighRate
#print axioms StratonovichHAMSecondMoment.WeakSobolev.rayleighRate
#check @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.memH1
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.memH1
#check @StratonovichHAMSecondMoment.WeakSobolev.rayleighValue_indep
#print axioms StratonovichHAMSecondMoment.WeakSobolev.rayleighValue_indep
#check @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.dil
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.dil
#check @StratonovichHAMSecondMoment.WeakSobolev.rayleighSet_dil
#print axioms StratonovichHAMSecondMoment.WeakSobolev.rayleighSet_dil
#check @StratonovichHAMSecondMoment.WeakSobolev.sqrt_sSup_scale
#print axioms StratonovichHAMSecondMoment.WeakSobolev.sqrt_sSup_scale
#check @StratonovichHAMSecondMoment.WeakSobolev.sSup_rayleighSet_dil
#print axioms StratonovichHAMSecondMoment.WeakSobolev.sSup_rayleighSet_dil
#check @StratonovichHAMSecondMoment.WeakSobolev.rayleighRate_dil
#print axioms StratonovichHAMSecondMoment.WeakSobolev.rayleighRate_dil
#check @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.memLp_f
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.memLp_f
#check @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.memLp_g
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.memLp_g
#check @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.weakGrad
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.weakGrad
#check @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.unit
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.unit
#check @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.integrable_pot
#print axioms StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial.integrable_pot
#check @StratonovichHAMSecondMoment.VariationalDilation.CPos
#print axioms StratonovichHAMSecondMoment.VariationalDilation.CPos
#check @StratonovichHAMSecondMoment.VariationalDilation.dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.dil
#check @StratonovichHAMSecondMoment.VariationalDilation.CPos_nonempty
#print axioms StratonovichHAMSecondMoment.VariationalDilation.CPos_nonempty
#check @StratonovichHAMSecondMoment.VariationalDilation.dilHomeo
#print axioms StratonovichHAMSecondMoment.VariationalDilation.dilHomeo
#check @StratonovichHAMSecondMoment.VariationalDilation.dil_mapsTo
#print axioms StratonovichHAMSecondMoment.VariationalDilation.dil_mapsTo
#check @StratonovichHAMSecondMoment.VariationalDilation.dil_inv_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.dil_inv_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.dil_dil_inv
#print axioms StratonovichHAMSecondMoment.VariationalDilation.dil_dil_inv
#check @StratonovichHAMSecondMoment.VariationalDilation.dil_bijOn
#print axioms StratonovichHAMSecondMoment.VariationalDilation.dil_bijOn
#check @StratonovichHAMSecondMoment.VariationalDilation.SetScaling
#print axioms StratonovichHAMSecondMoment.VariationalDilation.SetScaling
#check @StratonovichHAMSecondMoment.VariationalDilation.map_dilation
#print axioms StratonovichHAMSecondMoment.VariationalDilation.map_dilation
#check @StratonovichHAMSecondMoment.VariationalDilation.integral_dilation
#print axioms StratonovichHAMSecondMoment.VariationalDilation.integral_dilation
#check @StratonovichHAMSecondMoment.VariationalDilation.integrable_dilation_iff
#print axioms StratonovichHAMSecondMoment.VariationalDilation.integrable_dilation_iff
#check @StratonovichHAMSecondMoment.VariationalDilation.conv
#print axioms StratonovichHAMSecondMoment.VariationalDilation.conv
#check @StratonovichHAMSecondMoment.VariationalDilation.mean
#print axioms StratonovichHAMSecondMoment.VariationalDilation.mean
#check @StratonovichHAMSecondMoment.VariationalDilation.rawCost
#print axioms StratonovichHAMSecondMoment.VariationalDilation.rawCost
#check @StratonovichHAMSecondMoment.VariationalDilation.rate
#print axioms StratonovichHAMSecondMoment.VariationalDilation.rate
#check @StratonovichHAMSecondMoment.VariationalDilation.integratedRate
#print axioms StratonovichHAMSecondMoment.VariationalDilation.integratedRate
#check @StratonovichHAMSecondMoment.VariationalDilation.amp_mul_push
#print axioms StratonovichHAMSecondMoment.VariationalDilation.amp_mul_push
#check @StratonovichHAMSecondMoment.VariationalDilation.amp_variance
#print axioms StratonovichHAMSecondMoment.VariationalDilation.amp_variance
#check @StratonovichHAMSecondMoment.VariationalDilation.conv_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.conv_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.conv_dil_integrable_iff
#print axioms StratonovichHAMSecondMoment.VariationalDilation.conv_dil_integrable_iff
#check @StratonovichHAMSecondMoment.VariationalDilation.mean_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.mean_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.mean_dil_integrable_iff
#print axioms StratonovichHAMSecondMoment.VariationalDilation.mean_dil_integrable_iff
#check @StratonovichHAMSecondMoment.VariationalDilation.cost_integrand_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.cost_integrand_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.cost_inner_integrable_iff
#print axioms StratonovichHAMSecondMoment.VariationalDilation.cost_inner_integrable_iff
#check @StratonovichHAMSecondMoment.VariationalDilation.cost_inner_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.cost_inner_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.rawCost_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.rawCost_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.rawCost_integrable_iff
#print axioms StratonovichHAMSecondMoment.VariationalDilation.rawCost_integrable_iff
#check @StratonovichHAMSecondMoment.VariationalDilation.rayleighSet_mean_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.rayleighSet_mean_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.sSup_rayleighSet_mean_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.sSup_rayleighSet_mean_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.rate_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.rate_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.rate_integrable_iff
#print axioms StratonovichHAMSecondMoment.VariationalDilation.rate_integrable_iff
#check @StratonovichHAMSecondMoment.VariationalDilation.integratedRate_dil
#print axioms StratonovichHAMSecondMoment.VariationalDilation.integratedRate_dil
#check @StratonovichHAMSecondMoment.VariationalDilation.setScaling_of_homog
#print axioms StratonovichHAMSecondMoment.VariationalDilation.setScaling_of_homog
#check @StratonovichHAMSecondMoment.VariationalDilation.variational_control_dilation_paper
#print axioms StratonovichHAMSecondMoment.VariationalDilation.variational_control_dilation_paper
#check @StratonovichHAMSecondMoment.VariationalDilation.variational_control_dilation_integrable_paper
#print axioms StratonovichHAMSecondMoment.VariationalDilation.variational_control_dilation_integrable_paper
open MeasureTheory in
/-- Consumer (the use in `P:variational-positive-scores`, TeX lines 296-303):
along the dilation orbit of a control, the variational value
`c I - v/2` becomes `c r I_Ψ - r^{4-α} v_Ψ / 2`. -/
private theorem score_along_orbit_consumer {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (hH : StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    (hΓ0 : Γ ≠ 0) {r c : ℝ} (hr : 0 < r)
    (Ψ : ℝ × StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ)
    (hΨ : Ψ ∈ StratonovichHAMSecondMoment.VariationalDilation.CPos d) :
    StratonovichHAMSecondMoment.VariationalDilation.dil alpha r Ψ ∈
        StratonovichHAMSecondMoment.VariationalDilation.CPos d ∧
      c * StratonovichHAMSecondMoment.VariationalDilation.integratedRate alpha0 Γ
          (StratonovichHAMSecondMoment.VariationalDilation.dil alpha r Ψ) -
        StratonovichHAMSecondMoment.VariationalDilation.rawCost alpha0 Γ
          (StratonovichHAMSecondMoment.VariationalDilation.dil alpha r Ψ) / 2 =
      c * r * StratonovichHAMSecondMoment.VariationalDilation.integratedRate alpha0 Γ Ψ -
        r ^ (4 - alpha) * StratonovichHAMSecondMoment.VariationalDilation.rawCost alpha0 Γ Ψ / 2 := by
  obtain ⟨-, hbij, h⟩ :=
    StratonovichHAMSecondMoment.VariationalDilation.variational_control_dilation_paper hH hΓ0 hr
  obtain ⟨-, hv, -, hI⟩ := h Ψ hΨ
  refine ⟨hbij.mapsTo hΨ, ?_⟩
  rw [hv, hI]; ring
#check @score_along_orbit_consumer
#print axioms score_along_orbit_consumer
example (d : ℕ) : (StratonovichHAMSecondMoment.VariationalDilation.CPos d).Nonempty :=
  StratonovichHAMSecondMoment.VariationalDilation.CPos_nonempty d
example (d : ℕ) (V : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ) :
    StratonovichHAMSecondMoment.WeakSobolev.rayleighRate (fun x => (3 : ℝ) ^ 2 * V ((3 : ℝ) • x)) =
      3 * StratonovichHAMSecondMoment.WeakSobolev.rayleighRate V :=
  StratonovichHAMSecondMoment.WeakSobolev.rayleighRate_dil V (by norm_num)
