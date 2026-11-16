/-
Refutation for the domination hypothesis of the Lean engine that differentiates
under the integral sign (TeX lines 103-104 and 111-114 of
`notes/integrated_unmasked_variational.tex` at 39f2597a: the integrals are
finite because the integrands are dominated by integrable functions), package
theorem `StratonovichHAMSecondMoment.VariationalMeanDerivatives.integrable_tInt`.

Wrong variant: `integrable_tInt` without its hypothesis `Dominated`: every
`Good` function has an integrable weighted translate.  Counterexample: `E = ℝ`,
`ν` = Lebesgue measure, `τ = id`, `w = 1`, `S = univ`, `Φ = 1`: `Φ` is `Good`
(smooth, all derivatives bounded) but `y ↦ 1` is not Lebesgue integrable on
`ℝ`.  `domination_contrast` applies the package theorem with `ν = δ_0`, where
the domination holds with `g = 1`.
Class (b): a Lean-route-only control (the engine has no manuscript label).
Junk reliance: none.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalMeanDerivatives

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment VariationalMeanDerivatives

namespace Refutations.VariationalMeanDerivatives.Domination

/-- The constant `1` on `ℝ` is `Good` on `univ`. -/
theorem good_one : Good (univ : Set ℝ) (fun _ : ℝ => (1 : ℝ)) where
  smooth := contDiff_const
  supp := subset_univ _
  bdd n := by
    refine ⟨1, fun q => ?_⟩
    rcases n with _ | n
    · simp
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp

/-- Without domination, a `Good` function can have a non-integrable translate. -/
theorem integrable_without_domination_false :
    ¬ (∀ Φ : ℝ → ℝ, Good (univ : Set ℝ) Φ →
      Integrable (fun y : ℝ => (1 : ℝ) • Φ (0 - id y)) volume) := by
  intro h
  have := h _ good_one
  simp only [smul_eq_mul, mul_one] at this
  rw [integrable_const_iff] at this
  simp only [one_ne_zero, false_or] at this
  exact (measure_lt_top (volume : Measure ℝ) univ).ne (by simp)

/-- The package theorem with `ν = δ_0`, where the domination holds. -/
theorem domination_contrast :
    Integrable (fun y : ℝ => (1 : ℝ) • (fun _ : ℝ => (1 : ℝ)) (0 - id y))
      (Measure.dirac (0 : ℝ)) := by
  have hdom : Dominated (Measure.dirac (0 : ℝ)) id (fun _ => (1 : ℝ)) (univ : Set ℝ) :=
    fun _ => ⟨fun _ => 1, integrable_const _, fun _ => zero_le_one, fun _ _ _ _ => by simp⟩
  exact integrable_tInt measurable_id aestronglyMeasurable_const hdom good_one 0

end Refutations.VariationalMeanDerivatives.Domination
