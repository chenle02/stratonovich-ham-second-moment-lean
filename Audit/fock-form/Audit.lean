module

import StratonovichHAMSecondMoment.FockForm

set_option autoImplicit false
set_option pp.all true

#check @StratonovichHAMSecondMoment.FockForm.FockColumn
#print axioms StratonovichHAMSecondMoment.FockForm.FockColumn
#check @StratonovichHAMSecondMoment.FockForm.symm_of_isSelfAdjoint
#print axioms StratonovichHAMSecondMoment.FockForm.symm_of_isSelfAdjoint
#check @StratonovichHAMSecondMoment.FockForm.norm_proj_le
#print axioms StratonovichHAMSecondMoment.FockForm.norm_proj_le
#check @StratonovichHAMSecondMoment.FockForm.compress_symm
#print axioms StratonovichHAMSecondMoment.FockForm.compress_symm
#check @StratonovichHAMSecondMoment.FockForm.fockColumn_compress
#print axioms StratonovichHAMSecondMoment.FockForm.fockColumn_compress
#check @StratonovichHAMSecondMoment.FockForm.fock_const_eq
#print axioms StratonovichHAMSecondMoment.FockForm.fock_const_eq
#check @StratonovichHAMSecondMoment.FockForm.fock_form
#print axioms StratonovichHAMSecondMoment.FockForm.fock_form
#check @StratonovichHAMSecondMoment.FockForm.fock_form_paper
#print axioms StratonovichHAMSecondMoment.FockForm.fock_form_paper
#check @StratonovichHAMSecondMoment.FockForm.interval_contractions
#print axioms StratonovichHAMSecondMoment.FockForm.interval_contractions
#check @StratonovichHAMSecondMoment.FockForm.interval_contractions_paper
#print axioms StratonovichHAMSecondMoment.FockForm.interval_contractions_paper
#check @StratonovichHAMSecondMoment.FockForm.occupied_multiplication
#print axioms StratonovichHAMSecondMoment.FockForm.occupied_multiplication
#check @StratonovichHAMSecondMoment.FockForm.occupied_multiplication_paper
#print axioms StratonovichHAMSecondMoment.FockForm.occupied_multiplication_paper
#check @StratonovichHAMSecondMoment.FockForm.GoodDeg
#print axioms StratonovichHAMSecondMoment.FockForm.GoodDeg
#check @StratonovichHAMSecondMoment.FockForm.truncC
#print axioms StratonovichHAMSecondMoment.FockForm.truncC
#check @StratonovichHAMSecondMoment.FockForm.goodDeg_vac
#print axioms StratonovichHAMSecondMoment.FockForm.goodDeg_vac
#check @StratonovichHAMSecondMoment.FockForm.goodDeg_insert
#print axioms StratonovichHAMSecondMoment.FockForm.goodDeg_insert
#check @StratonovichHAMSecondMoment.FockForm.goodDeg_frame
#print axioms StratonovichHAMSecondMoment.FockForm.goodDeg_frame
#check @StratonovichHAMSecondMoment.FockForm.truncC_eq
#print axioms StratonovichHAMSecondMoment.FockForm.truncC_eq

open MeasureTheory ProbabilityTheory StratonovichHAMSecondMoment
open scoped Pointwise

namespace StratonovichHAMSecondMoment.Audit.FockForm

open StratonovichHAMSecondMoment.FockForm StratonovichHAMSecondMoment.HermiteFock

/-- Consumer of `occupied_multiplication_paper`: for one standard Gaussian `g`
and `H = F = g`, `‖g²‖₂ ≤ 2√2 ‖g‖₂ ‖g‖₂`. -/
private theorem audit_consumer {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    [IsProbabilityMeasure Pr] (g : Fin 1 → Ω → ℝ) (hind : iIndepFun g Pr)
    (hlaw : ∀ i, HasLaw (g i) (gaussianReal 0 1) Pr) :
    √(∫ ω, ((∑ i, (fun _ => (1 : ℝ)) i * g i ω) *
        MvPolynomial.eval (fun i => g i ω) (MvPolynomial.X 0)) ^ 2 ∂Pr) ≤
      2 * √(((1 : ℕ) : ℝ) + 1) * √(∫ ω, (∑ i, (fun _ => (1 : ℝ)) i * g i ω) ^ 2 ∂Pr) *
        √(∫ ω, (MvPolynomial.eval (fun i => g i ω)
          (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℝ)) ^ 2 ∂Pr) :=
  (occupied_multiplication_paper g hind hlaw 1 _ _ (by simp)).2.2.2

/-- Consumer of `fock_form_paper`: the scalar Fock bound with the zero spatial
family (every column bound holds). -/
private theorem audit_consumer_fock (Γ μ : Measure (HomogHypothesis.Rd 3))
    (hΓ : IsLocallyFiniteMeasure Γ) (hμ : IsLocallyFiniteMeasure μ)
    (hΓe : HomogHypothesis.IsEven Γ) (hΓt : HomogHypothesis.IsTempered Γ)
    (hΓp : HomogHypothesis.IsPosDefDistr Γ) (hspec : HomogHypothesis.IsSpectralMeasure Γ μ)
    (hscal : ∀ A : Set (HomogHypothesis.Rd 3), MeasurableSet A → ∀ c : ℝ, 0 < c →
      Γ (c • A) = ENNReal.ofReal (c ^ ((3 : ℝ) - 1)) * Γ A)
    (N : ℕ) {v : (Fin 1 → ℕ) → ℂ} (hv : Supp N v) :
    ∑ k ∈ degLE 1 N, ‖fieldOp (fun _ => ContinuousLinearMap.id ℂ ℂ ∘L
        (0 : ℂ →L[ℂ] ℂ) ∘L ContinuousLinearMap.id ℂ ℂ) v k‖ ^ 2 ≤
      (StaticPhaseCauchy.fockD N (1 * Real.pi * (μ (Metric.ball 0 1)).toReal /
        (2 * Real.sin (Real.pi * 1 / 2))) * (1 : ℝ) ^ ((1 : ℝ) / 2 - 2)) ^ 2 *
        ∑ k ∈ degLE 1 N, ‖v k‖ ^ 2 :=
  (fock_form_paper (ε := 1) Γ μ hΓ hμ hΓe hΓt hΓp hspec hscal one_pos one_lt_two rfl one_pos one_pos
    (fun _ => 0) (fun _ => IsSelfAdjoint.zero _)
    (fun u => by
      simp
      exact mul_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le ENNReal.toReal_nonneg)
        (by norm_num)) (sq_nonneg _))
    (ContinuousLinearMap.id ℂ ℂ) (IsSelfAdjoint.one _) (by ext; simp) N hv).1

#check @audit_consumer
#print axioms audit_consumer
#check @audit_consumer_fock
#print axioms audit_consumer_fock

end StratonovichHAMSecondMoment.Audit.FockForm
