/-
Refutation for the integer check of `C:intrinsic-spatial-bracket`, package theorem
`StratonovichHAMSecondMoment.SpatialBracket.counterexample_integers`
(`integrated_occupation_ceiling.tex` lines 294-298 at a284420:
`11^11 7^7 = 234966429149994773 < 4803028329503971872 = 2^5 9^18`).

Wrong variant: the factor `2^5` (from `-(α/2) log 2` with `α = 5/4`, times 8) is dropped, i.e.
`11^11 7^7 < 9^18`.  Counterexample: `9^18 = 150094635296999121 < 234966429149994773`.
`integer_order_contrast` is the package inequality.
No junk-value reliance (natural numbers).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialBracket

set_option autoImplicit false

open StratonovichHAMSecondMoment.SpatialBracket

namespace Refutations.SpatialBracket

/-- Without the factor `2^5` the order of the two integers is reversed. -/
theorem integer_order_refuted : ¬ ((11 : ℕ) ^ 11 * 7 ^ 7 < 9 ^ 18) := by
  norm_num

/-- The package inequality `11^11 7^7 < 2^5 9^18`. -/
theorem integer_order_contrast : (11 : ℕ) ^ 11 * 7 ^ 7 < 2 ^ 5 * 9 ^ 18 :=
  counterexample_integers.2.2

end Refutations.SpatialBracket
