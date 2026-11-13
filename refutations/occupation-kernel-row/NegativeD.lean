/-
Refutation for the hypothesis `D > 0` of `L:occupation-kernel-row`
(`notes/integrated_spatial_occupation.tex`, lines 4-10 and 352-379 at a284420),
package definitions `kstarIntegrand`, `Kstar` and package theorems
`kstarIntegrand_integrable`, `Kstar_pos`.

Wrong variant: drop `D > 0`.  At `D = -1`, `a = 1/2`, `u = 1` the integrand
`e^{-(λ - λ²/2)} λ^{-1/2}` of `E:occupation-damped-kernel` is at least
`λ^{-1/2}` for `λ ≥ 2`, so it is not integrable on `(0,∞)`
(`negD_not_integrable`, a statement with no junk value: the manuscript's
integral is `+∞`).  JUNK-VALUE RELIANCE (stated): Lean's Bochner integral of a
non-integrable function is `0`, so the package `Kstar (1/2) (-1) 1` is `0`, and
the positivity clause fails (`positivity_without_hD_false`); this second
statement records how the Lean definition behaves, the mathematical content is
`negD_not_integrable`.  `negD_contrast` applies the package theorems at `D = 1`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationKernelRow

set_option autoImplicit false

open MeasureTheory Set Filter

namespace Refutations.OccupationKernelRow

open StratonovichHAMSecondMoment.OccupationKernelRow StratonovichHAMSecondMoment.TimeFractional

/-- Refuted variant of `kstarIntegrand_integrable` with `D > 0` dropped. -/
theorem negD_not_integrable : ¬ Integrable (kstarIntegrand (1 / 2) (-1) 1) L0 := by
  intro h
  have h2 : IntegrableOn (kstarIntegrand (1 / 2) (-1) 1) (Ioi 2) :=
    (show IntegrableOn (kstarIntegrand (1 / 2) (-1) 1) (Ioi (0 : ℝ)) volume from h).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2))
  have hpow : IntegrableOn (fun l : ℝ => l ^ ((1 / 2 : ℝ) - 1)) (Ioi 2) := by
    refine Integrable.mono' h2 (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l hl => ?_)
    have hl : (2 : ℝ) < l := hl
    have hl0 : (0 : ℝ) < l := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _)]
    unfold kstarIntegrand
    have hE : 1 ≤ Real.exp (-(l + l ^ 2 / (2 * -1)) * |(1 : ℝ)|) := by
      rw [Real.one_le_exp_iff]
      have e : -(l + l ^ 2 / (2 * -1)) * |(1 : ℝ)| = l * (l - 2) / 2 := by
        rw [abs_one]; ring
      rw [e]
      exact div_nonneg (mul_nonneg hl0.le (by linarith)) (by norm_num)
    have hp : 0 ≤ l ^ ((1 / 2 : ℝ) - 1) := Real.rpow_nonneg hl0.le _
    nlinarith
  rw [integrableOn_Ioi_rpow_iff (by norm_num)] at hpow
  norm_num at hpow

/-- JUNK-VALUE RELIANCE: refuted variant of `Kstar_pos` with `D > 0` dropped (the Lean
value is `0` because the defining integral diverges). -/
theorem positivity_without_hD_false :
    ¬ ∀ a D u : ℝ, 0 < a → u ≠ 0 → 0 < Kstar a D u := by
  intro h
  have h1 := h (1 / 2) (-1) 1 (by norm_num) one_ne_zero
  have h0 : Kstar (1 / 2) (-1) 1 = 0 := by
    simp only [Kstar, one_ne_zero, ite_false]
    rw [integral_undef negD_not_integrable, mul_zero]
  rw [h0] at h1
  exact lt_irrefl _ h1

/-- Contrast: with `D = 1 > 0` the package proves integrability and positivity. -/
theorem negD_contrast :
    Integrable (kstarIntegrand (1 / 2) 1 1) L0 ∧ 0 < Kstar (1 / 2) 1 1 :=
  ⟨kstarIntegrand_integrable _ _ _ (by norm_num) one_pos one_ne_zero,
    Kstar_pos _ _ _ (by norm_num) one_pos one_ne_zero⟩

end Refutations.OccupationKernelRow
