/-
Refutation for the time-kernel integrability on bounded intervals used in the
first sentence of `L:variational-global-mean`
(`notes/integrated_unmasked_variational.tex` lines 111-113 at edf7085f: "integrable
since `a < 1`"), package theorem
`StratonovichHAMSecondMoment.VariationalMeanDerivatives.abs_rpow_integrableOn_Ioo`.

Wrong variant: the hypothesis `a < 1` (from `α₀ < 1` in `H:homog`) relaxed
to `a ≤ 1`.  Counterexample: `a = 1`, `T = 2`: `r ↦ |r|^{-1}` is not
integrable on `(-2,2)` (already not on `(0,1)`, Mathlib's
`integrableOn_Ioo_rpow_iff`).  `kernel_bounded_contrast` applies the package
theorem at `a = 1/2`, `T = 2`.
Class (c): a broader Lean generalization outside the manuscript domain
(`α₀ < 1`).  Junk reliance: none.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalMeanDerivatives

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment VariationalMeanDerivatives

namespace Refutations.VariationalMeanDerivatives.Kernel

/-- `|r|^{-1}` is not integrable on `(-2,2)`. -/
theorem kernel_exponent_one_bounded_false :
    ¬ IntegrableOn (fun r : ℝ => |r| ^ (-(1 : ℝ))) (Ioo (-2) 2) := by
  intro h
  have h1 : IntegrableOn (fun r : ℝ => r ^ (-(1 : ℝ))) (Ioo 0 1) := by
    refine (h.mono_set (Ioo_subset_Ioo (by norm_num) (by norm_num))).congr_fun
      (fun r hr => ?_) measurableSet_Ioo
    simp [abs_of_pos hr.1]
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(1 : ℝ)) one_pos).1 h1
  norm_num at this

/-- The relaxed hypothesis `a ≤ 1` would give integrability at `a = 1`. -/
theorem relaxed_kernel_hypothesis_false :
    ¬ (∀ a : ℝ, a ≤ 1 → ∀ T : ℝ, IntegrableOn (fun r : ℝ => |r| ^ (-a)) (Ioo (-T) T)) :=
  fun h => kernel_exponent_one_bounded_false (h 1 le_rfl 2)

/-- The package theorem at `a = 1/2`, `T = 2`. -/
theorem kernel_bounded_contrast :
    IntegrableOn (fun r : ℝ => |r| ^ (-(1 / 2 : ℝ))) (Ioo (-2) 2) :=
  abs_rpow_integrableOn_Ioo (by norm_num) 2

end Refutations.VariationalMeanDerivatives.Kernel
