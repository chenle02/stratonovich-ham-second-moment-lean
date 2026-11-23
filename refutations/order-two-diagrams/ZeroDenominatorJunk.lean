/-
Refutation for the range `α₀ < 1` of the closed forms of `L:white-test` (main TeX
lines 941-942 at edf7085f: `c_0 = ((1-α₀)(2-α₀)(3-α₀))^{-1}`), package definition
`StratonovichHAMSecondMoment.OrderTwoDiagrams.c0` and theorem `c0_pos`.

Wrong variant: the constant is positive also at `α₀ = 1`.  In Lean
`c0 1 = (0 · 1 · 2)⁻¹ = 0` (division by zero is `0`), so the formula
`c_0 t^{3-α₀}` would assign the junk value `0` to a diagram whose time integral
`∫ |s - r|^{-1}` diverges; the package theorems therefore assume `α₀ < 1`.
`zeroDenominatorJunk_contrast` is `c0_pos` at `α₀ = 1/2`.
Class (c): control of Lean's totalized arithmetic outside the manuscript domain.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OrderTwoDiagrams

set_option autoImplicit false

open StratonovichHAMSecondMoment OrderTwoDiagrams

namespace Refutations.OrderTwoDiagrams

/-- The package: `c_0 > 0` at `α₀ = 1/2`. -/
theorem zeroDenominatorJunk_contrast : 0 < c0 (1 / 2) := c0_pos (by norm_num)

/-- At `α₀ = 1` Lean's `c_0` is the junk value `0`. -/
theorem zeroDenominatorJunk_refuted : ¬ 0 < c0 1 := by
  simp [c0]

end Refutations.OrderTwoDiagrams
