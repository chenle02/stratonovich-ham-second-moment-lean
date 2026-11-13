/-
Refutation for the time-kernel integrability used in
`L:variational-global-mean` (`notes/integrated_unmasked_variational.tex`
lines 89-91 at a284420: "integrable since `a < 1`"), package theorem
`StratonovichHAMSecondMoment.VariationalMean.abs_rpow_integrableOn`.

Wrong variant: the hypothesis `a < 1` (from `α₀ < 1` in `H:homog`) relaxed
to `a ≤ 1`.  Counterexample: `a = 1`: `r ↦ |r|^{-1}` is not integrable on
`(-1,1)` (already not on `(0,1)`, Mathlib's `integrableOn_Ioo_rpow_iff`).
`kernel_contrast` applies the package theorem at `a = 1/2`.
Junk reliance: none (`|0|^{-1}` is a single point).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalMean

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment VariationalMean

namespace Refutations.VariationalMean.Kernel

/-- `|r|^{-1}` is not integrable on `(-1,1)`. -/
theorem kernel_exponent_one_false :
    ¬ IntegrableOn (fun r : ℝ => |r| ^ (-(1 : ℝ))) (Ioo (-1) 1) := by
  intro h
  have h1 : IntegrableOn (fun r : ℝ => r ^ (-(1 : ℝ))) (Ioo 0 1) := by
    refine (h.mono_set (Ioo_subset_Ioo_left (by norm_num))).congr_fun (fun r hr => ?_)
      measurableSet_Ioo
    simp [abs_of_pos hr.1]
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(1 : ℝ)) one_pos).1 h1
  norm_num at this

/-- The relaxed hypothesis `a ≤ 1` would give integrability at `a = 1`. -/
theorem relaxed_hypothesis_false :
    ¬ (∀ a : ℝ, a ≤ 1 → IntegrableOn (fun r : ℝ => |r| ^ (-a)) (Ioo (-1) 1)) :=
  fun h => kernel_exponent_one_false (h 1 le_rfl)

/-- The package theorem at `a = 1/2`. -/
theorem kernel_contrast : IntegrableOn (fun r : ℝ => |r| ^ (-(1 / 2 : ℝ))) (Ioo (-1) 1) :=
  abs_rpow_integrableOn (by norm_num)

end Refutations.VariationalMean.Kernel
