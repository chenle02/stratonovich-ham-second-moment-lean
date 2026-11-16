module
import StratonovichHAMSecondMoment.VariationalMeanDerivatives
set_option autoImplicit false
set_option pp.all true
open StratonovichHAMSecondMoment
#check @VariationalMeanDerivatives.tInt
#print axioms VariationalMeanDerivatives.tInt
#check @VariationalMeanDerivatives.Good
#print axioms VariationalMeanDerivatives.Good
#check @VariationalMeanDerivatives.Dominated
#print axioms VariationalMeanDerivatives.Dominated
#check @VariationalMeanDerivatives.Good.fderiv
#print axioms VariationalMeanDerivatives.Good.fderiv
#check @VariationalMeanDerivatives.Good.norm_le
#print axioms VariationalMeanDerivatives.Good.norm_le
#check @VariationalMeanDerivatives.Good.iteratedFDeriv_eq_zero
#print axioms VariationalMeanDerivatives.Good.iteratedFDeriv_eq_zero
#check @VariationalMeanDerivatives.Good.eq_zero
#print axioms VariationalMeanDerivatives.Good.eq_zero
#check @VariationalMeanDerivatives.wbound
#print axioms VariationalMeanDerivatives.wbound
#check @VariationalMeanDerivatives.meas_integrand
#print axioms VariationalMeanDerivatives.meas_integrand
#check @VariationalMeanDerivatives.integrable_tInt
#print axioms VariationalMeanDerivatives.integrable_tInt
#check @VariationalMeanDerivatives.hasFDerivAt_tInt
#print axioms VariationalMeanDerivatives.hasFDerivAt_tInt
#check @VariationalMeanDerivatives.fderiv_tInt
#print axioms VariationalMeanDerivatives.fderiv_tInt
#check @VariationalMeanDerivatives.contDiff_tInt_nat
#print axioms VariationalMeanDerivatives.contDiff_tInt_nat
#check @VariationalMeanDerivatives.contDiff_tInt
#print axioms VariationalMeanDerivatives.contDiff_tInt
#check @VariationalMeanDerivatives.norm_iteratedFDeriv_tInt_le
#print axioms VariationalMeanDerivatives.norm_iteratedFDeriv_tInt_le
#check @VariationalMeanDerivatives.τ₁
#print axioms VariationalMeanDerivatives.τ₁
#check @VariationalMeanDerivatives.S₁
#print axioms VariationalMeanDerivatives.S₁
#check @VariationalMeanDerivatives.S₂
#print axioms VariationalMeanDerivatives.S₂
#check @VariationalMeanDerivatives.τ₂
#print axioms VariationalMeanDerivatives.τ₂
#check @VariationalMeanDerivatives.w₂
#print axioms VariationalMeanDerivatives.w₂
#check @VariationalMeanDerivatives.measurable_τ₁
#print axioms VariationalMeanDerivatives.measurable_τ₁
#check @VariationalMeanDerivatives.measurable_τ₂
#print axioms VariationalMeanDerivatives.measurable_τ₂
#check @VariationalMeanDerivatives.tInt_one_eq_conv
#print axioms VariationalMeanDerivatives.tInt_one_eq_conv
#check @VariationalMeanDerivatives.pt_bound_norm
#print axioms VariationalMeanDerivatives.pt_bound_norm
#check @VariationalMeanDerivatives.good_ctrl
#print axioms VariationalMeanDerivatives.good_ctrl
#check @VariationalMeanDerivatives.dominated₁
#print axioms VariationalMeanDerivatives.dominated₁
#check @VariationalMeanDerivatives.good_conv
#print axioms VariationalMeanDerivatives.good_conv
#check @VariationalMeanDerivatives.abs_rpow_integrableOn_Ioo
#print axioms VariationalMeanDerivatives.abs_rpow_integrableOn_Ioo
#check @VariationalMeanDerivatives.measurable_w₂
#print axioms VariationalMeanDerivatives.measurable_w₂
#check @VariationalMeanDerivatives.slab_bound
#print axioms VariationalMeanDerivatives.slab_bound
#check @VariationalMeanDerivatives.dominated₂
#print axioms VariationalMeanDerivatives.dominated₂
#check @VariationalMeanDerivatives.mean_eq_tInt
#print axioms VariationalMeanDerivatives.mean_eq_tInt
#check @VariationalMeanDerivatives.mean_derivatives
#print axioms VariationalMeanDerivatives.mean_derivatives
#check @VariationalMeanDerivatives.mean_partial_bound
#print axioms VariationalMeanDerivatives.mean_partial_bound
#check @VariationalMeanDerivatives.variational_global_mean_derivatives_paper
#print axioms VariationalMeanDerivatives.variational_global_mean_derivatives_paper
#check @VariationalMeanDerivatives.variational_global_mean_whole_paper
#print axioms VariationalMeanDerivatives.variational_global_mean_whole_paper
set_option pp.all false

namespace StratonovichHAMSecondMoment.Audit.VariationalMeanDerivatives

open MeasureTheory Set StratonovichHAMSecondMoment HomogHypothesis VariationalDilation
open VariationalMeanDerivatives

/-- Consumer of `variational_global_mean_whole_paper`: under the section's
hypotheses, the time derivative `∂_s h` (the first Fréchet derivative applied to
`(1,0)`) is bounded on `[0,1] × ℝ^d`, and `h_s` is bounded above on `[0,1]`. -/
theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    (∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : Rd d,
      |fderiv ℝ (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) (s, x) (1, 0)| ≤ C) ∧
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, mean alpha0 Γ Ψ s x ≤ M := by
  obtain ⟨⟨-, -, hb⟩, M, -, -, -, h3, -⟩ := variational_global_mean_whole_paper hH hΓ0 hΨ
  obtain ⟨C, -, hC⟩ := hb 1 (Icc 0 1) isCompact_Icc
  refine ⟨⟨C * ‖((1 : ℝ), (0 : Rd d))‖, fun s hs x => ?_⟩, M, fun s hs x => (h3 s hs x).2⟩
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) (s, x)).le_opNorm
    (1, 0)).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [← norm_iteratedFDeriv_one]
  exact hC s hs x

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.VariationalMeanDerivatives
