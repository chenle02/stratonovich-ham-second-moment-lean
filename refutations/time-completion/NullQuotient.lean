/-
Refutation for the null quotient of `L:masked-time-completion`
(`notes/integrated_covariance_foundation.tex` lines 147-148 at a284420), package
definitions `StratonovichHAMSecondMoment.TimeCompletion.Ha` and `emb`.

Wrong variant: the inclusion `emb : L²(0,T) → H_a` is injective on functions, i.e. the
completion keeps distinct functions distinct (no null quotient).  Counterexample:
`a = 1/2`, `T = 1`, `f = 1_{{0}}` (the indicator of the point `0`) and `g = 0`:
`f ≠ g` as functions, but they agree a.e., so `emb f = emb g`.
`null_quotient_contrast` is the package lemma `coe_eq_of_ae` at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TimeCompletion

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment TimeCompletion

namespace Refutations.TimeCompletion

/-- The parameters `a = 1/2`, `T = 1`. -/
noncomputable abbrev pHalf : TimeParams := ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩

/-- `1_{{0}}` is a.e. zero on `[0,1]`. -/
theorem indicator_zero_ae :
    ({0} : Set ℝ).indicator (fun _ => (1 : ℂ)) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] 0 := by
  have h0 : volume.restrict (Icc (0 : ℝ) 1) {0} = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans (by simp)) bot_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with t ht
  simp [indicator_of_notMem ht]

/-- The point indicator, as an element of `L²(0,1)`. -/
noncomputable def ptInd : L2fun pHalf.T :=
  ⟨({0} : Set ℝ).indicator (fun _ => (1 : ℂ)), MemLp.zero.ae_eq indicator_zero_ae.symm⟩

/-- The package lemma: functions agreeing a.e. have the same image in `H_a`. -/
theorem null_quotient_contrast : emb pHalf ptInd = emb pHalf 0 :=
  coe_eq_of_ae (toPre ptInd) (toPre (0 : L2fun pHalf.T)) indicator_zero_ae

/-- Injectivity of `emb` on functions is false. -/
theorem null_quotient_refuted :
    ¬ (∀ f g : L2fun pHalf.T, emb pHalf f = emb pHalf g → f = g) := by
  intro h
  have := congrArg (fun f : L2fun pHalf.T => (f : ℝ → ℂ) 0) (h _ _ null_quotient_contrast)
  simp [ptInd] at this

end Refutations.TimeCompletion
