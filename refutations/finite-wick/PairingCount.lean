/-
Refutation for the pairing count of `FiniteWick` (the coefficient of the Wick
formula in `L:terminal-wick`, main TeX lines 3670-3673 at a284420: "orientations
and orderings of the `k` pairs cancel the exponential's `2^k k!` denominator"),
package theorem `StratonovichHAMSecondMoment.FiniteWick.card_pairings_even`.

Wrong variant: a `2k`-set has `(2k)!/k!` pairings (cancelling the `k!`
orderings but not the `2^k` orientations).  Counterexample: `k = 2`, the set
`Fin 4`: `(2·2)!/2! = 12`, while the package gives `(2·2-1)!! = 3`.
`pairing_count_contrast` is the package theorem at the same point.
No junk-value reliance (natural-number arithmetic only).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FiniteWick

set_option autoImplicit false

open StratonovichHAMSecondMoment FiniteWick

namespace Refutations.FiniteWick

/-- The package count at `Fin 4`: three pairings. -/
theorem pairing_count_contrast :
    (pairings (Finset.univ : Finset (Fin 4))).card = 3 := by
  rw [card_pairings_even 2 _ (by simp)]
  decide

/-- The count `(2k)!/k!` is false. -/
theorem pairing_count_refuted :
    ¬ (∀ k : ℕ, (pairings (Finset.univ : Finset (Fin (2 * k)))).card =
        (2 * k).factorial / k.factorial) := by
  intro h
  have h2 := h 2
  rw [pairing_count_contrast] at h2
  revert h2
  decide

end Refutations.FiniteWick
