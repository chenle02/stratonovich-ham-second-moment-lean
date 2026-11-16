module

import StratonovichHAMSecondMoment.TerminalWickComplete

set_option autoImplicit false
set_option pp.all true

open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.norm_sq_sum_smul
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.norm_sq_sum_smul
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.norm_sq_partial_le
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.norm_sq_partial_le
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.norm_sq_tsum_le
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.norm_sq_tsum_le
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.toC
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.toC
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.coeFn_toC
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.coeFn_toC
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.inner_toC
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.inner_toC
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.inner_self_eq_ofReal
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.inner_self_eq_ofReal
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.norm_toC
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.norm_toC
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.integral_norm_sq_eq
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.integral_norm_sq_eq
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.summable_norm_smul_toC
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.summable_norm_smul_toC
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.summable_smul_toC
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.summable_smul_toC
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.norm_sq_sum_smul_toC
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.norm_sq_sum_smul_toC
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.tendsto_norm_sq_tsum_toC
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.tendsto_norm_sq_tsum_toC
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.inner_odd_constructed
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.inner_odd_constructed
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.summable_constructed
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.summable_constructed
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.partial_sum_mono_constructed_paper
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.partial_sum_mono_constructed_paper
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.terminal_wick_complex_constructed_paper
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.terminal_wick_complex_constructed_paper
open StratonovichHAMSecondMoment in
#check @TerminalWickComplete.terminal_wick_full_constructed_paper
open StratonovichHAMSecondMoment in
#print axioms TerminalWickComplete.terminal_wick_full_constructed_paper

set_option pp.all false

open MeasureTheory Finset StratonovichHAMSecondMoment TerminalWick TerminalWickInputs
open TerminalWickComplete FiniteWick

namespace StratonovichHAMSecondMoment.Audit.TerminalWickComplete

/-- Consumer: the full wrapper yields, for `0 ≤ K₁ ≤ K₂`, the comparison of the second moments of
the order-2 partial sums at `r = -3`, and the convergence at the complex `r = i`. -/
private theorem audit_consumer {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T) (x : HomogHypothesis.Rd d)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (hV₁ : BddAbove (Set.range fun p => K₁ p p)) (hc₁ : MeanSquareCellContinuous K₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₂ : BddAbove (Set.range fun p => K₂ p p)) (hc₂ : MeanSquareCellContinuous K₂)
    (h0 : ∀ p q, 0 ≤ K₁ p q) (h12 : ∀ p q, K₁ p q ≤ K₂ p q) :
    (∫ ω, ((∑ n ∈ range 3, (-3 : ℝ) ^ n •
        chainIntegral (fun n => chainMeasure d n T hT.le x) hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
      ∫ ω, ((∑ n ∈ range 3, (-3 : ℝ) ^ n •
        chainIntegral (fun n => chainMeasure d n T hT.le x) hW₂ n : Lp ℝ 2 P₂) ω) ^ 2 ∂P₂) ∧
      Summable (fun n => Complex.I ^ n •
        toC (chainIntegral (fun n => chainMeasure d n T hT.le x) hW₁ n)) := by
  have h := terminal_wick_full_constructed_paper P₁ P₂ d hd T hT x W₁ K₁ hW₁ hV₁ hc₁
    W₂ K₂ hW₂ hV₂ hc₂
  exact ⟨(h.2.2 h0 h12).2.1 (-3) 2, (h.2.1.1 Complex.I).2⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.TerminalWickComplete
