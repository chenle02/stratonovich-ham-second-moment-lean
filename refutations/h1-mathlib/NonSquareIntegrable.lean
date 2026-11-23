/-
Refutation for the square-integrability clause of `H^1(ℝ^d; ℝ)` (main TeX
lines 748-750 at edf7085f: "the real Sobolev space of square-integrable
functions with square-integrable first weak derivatives"), package
definition `StratonovichHAMSecondMoment.WeakSobolev.MemH1` and the
identification `StratonovichHAMSecondMoment.H1Mathlib.memH1_iff_memSobolev`
(which takes `f ∈ L²` as a hypothesis).

Wrong variant: an `L²` weak gradient alone puts `f` in `H^1`, i.e. the clause
`f ∈ L²` can be dropped. Counterexample: `d = 1`, `f ≡ 1` has the weak
gradient `0 ∈ L²` (integration by parts against a test function) but is not
square-integrable on `ℝ` (infinite Lebesgue measure). Class (a): perturbation
of the manuscript definition in the manuscript domain (real functions on
`ℝ^d`). `non_square_integrable_contrast`: with `f ∈ L²` the weak-gradient
condition does give `MemH1`, hence Mathlib's `H^{1,2}`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.H1Mathlib

set_option autoImplicit false

namespace Refutations.H1Mathlib

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.H1Mathlib
open StratonovichHAMSecondMoment.WeakSobolev MeasureTheory TemperedDistribution
open HomogHypothesis (Rd)

/-- The constant `1` has the weak gradient `0`. -/
theorem hasWeakGradient_one : HasWeakGradient (fun _ : Rd 1 => (1 : ℝ)) (fun _ => 0) := by
  intro φ hφ v
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Rd 1 => (1 : ℝ)) (g := φ) (v := v)
    (by simp)
    (by
      simpa using ((hφ1.continuous_fderiv one_ne_zero).clm_apply
        continuous_const).integrable_of_hasCompactSupport
        ((hφ.2.fderiv ℝ).comp_left (g := fun L : Rd 1 →L[ℝ] ℝ => L v) (by simp)))
    (by simpa using hφ1.continuous.integrable_of_hasCompactSupport hφ.2)
    (fun x _ => differentiableAt_const _) (fun x _ => hφ1.differentiable one_ne_zero x)
  rw [key]
  simp

/-- An `L²` weak gradient does not force `f ∈ L²`. -/
theorem non_square_integrable :
    ¬ ∀ f : Rd 1 → ℝ, (∃ g : Rd 1 → Rd 1, MemLp g 2 volume ∧ HasWeakGradient f g) →
      MemH1 f := by
  intro H
  have h := (H (fun _ => 1) ⟨fun _ => 0, MemLp.zero, hasWeakGradient_one⟩).1
  have hinf : (volume : Measure (Rd 1)) Set.univ = ⊤ :=
    measure_univ_of_isAddLeftInvariant volume
  rw [memLp_const_iff (by norm_num) (by norm_num)] at h
  rcases h with h | h
  · norm_num at h
  · rw [hinf] at h; exact lt_irrefl _ h

/-- Contrast: with `f ∈ L²`, an `L²` weak gradient gives `MemH1 f` and so
Mathlib's `H^{1,2}`. -/
theorem non_square_integrable_contrast (f : Rd 1 → ℝ) (hf : MemLp f 2 volume)
    (hg : ∃ g : Rd 1 → Rd 1, MemLp g 2 volume ∧ HasWeakGradient f g) :
    MemH1 f ∧ MemSobolev 1 2 (toDistr hf) := by
  obtain ⟨g, hg, hw⟩ := hg
  exact ⟨⟨hf, g, hg, hw⟩, memSobolev_of_hasWeakGradient hf hg hw⟩

end Refutations.H1Mathlib
