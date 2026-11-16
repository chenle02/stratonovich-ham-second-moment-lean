/-
Refutation for the truncation of the time kernel in the first sentence of
`L:variational-global-mean` (`notes/integrated_unmasked_variational.tex` lines
111-112 at 39f2597a: "For `s` in a compact interval the relevant `r` lie in a
fixed bounded interval"), package theorem
`StratonovichHAMSecondMoment.VariationalMeanDerivatives.slab_bound`.

Wrong variant: `slab_bound` with the non-strict hypothesis `|s| ≤ T - 1`
instead of `|s| < T - 1` (the truncation interval `(-T, T)` is open).
Counterexample: `d = 1`, `T = 1`, `(s,x) = (0,0)`, `r = -1`: `s - r = 1 ∈ [0,1]`,
`|w₂ a (-1)| = 1`, but `-1 ∉ (-1,1)`, so the truncated kernel is `0`.
`slab_contrast` applies the package theorem at `T = 2`.
Class (b): a Lean-route-only control (the boundary convention of the Lean
truncation; the TeX's interval is not specified to that precision).
Junk reliance: none.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalMeanDerivatives

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment HomogHypothesis VariationalMeanDerivatives

namespace Refutations.VariationalMeanDerivatives.Slab

/-- The non-strict truncation hypothesis is false. -/
theorem slab_nonstrict_false :
    ¬ (∀ (a T : ℝ) (p : ℝ × Rd 1), |p.1| ≤ T - 1 → ∀ r : ℝ, p - τ₂ r ∈ S₂ (d := 1) →
      |w₂ a r| ≤ (Ioo (-T) T).indicator (fun r => |r| ^ (-a)) r) := by
  intro h
  have hS : ((0 : ℝ), (0 : Rd 1)) - τ₂ (-1) ∈ S₂ (d := 1) := by
    simp [S₂, τ₂]
  have := h 0 1 (0, 0) (by norm_num) (-1) hS
  rw [indicator_of_notMem (by simp)] at this
  norm_num [w₂] at this

/-- The package theorem at `T = 2`, `(s,x) = (0,0)`, `r = -1`. -/
theorem slab_contrast (a : ℝ) :
    |w₂ a (-1)| ≤ (Ioo (-2 : ℝ) 2).indicator (fun r => |r| ^ (-a)) (-1) := by
  refine slab_bound (p := ((0 : ℝ), (0 : Rd 1))) (by norm_num) (-1) ?_
  simp [S₂, τ₂]

end Refutations.VariationalMeanDerivatives.Slab
