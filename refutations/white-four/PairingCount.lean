/-
Refutation for "no unlisted pairing or multiplicity" (main TeX line 5001 at
39f2597a) and the three pairings `A, B, C` (lines 4911-4916), package theorem
`StratonovichHAMSecondMoment.WhiteFour.pairings_four`.

Wrong variant: `Π_2` on four labels contains a fourth pairing (for instance
the identity counted as the "empty pairing", or a pairing listed twice with
multiplicity).  The package shows the set is exactly `{A, B, C}`, so its
cardinality is `3`, not `4`.  `pairingCount_contrast` is the package count.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WhiteFour

set_option autoImplicit false

open StratonovichHAMSecondMoment DiagramModel WhiteFour

namespace Refutations.WhiteFour

/-- The package: `#Π_2 = 3` for the chains `(0,4)`. -/
theorem pairingCount_contrast : (Pi2 0 4).card = 3 := by
  rw [Pi2_04]; decide

/-- There is no fourth pairing; the identity is not one. -/
theorem pairingCount_refuted : ¬ ((Pi2 0 4).card = 4 ∨ (id : Fin 4 → Fin 4) ∈ Pi2 0 4) := by
  rintro (h | h)
  · rw [pairingCount_contrast] at h; exact absurd h (by norm_num)
  · rw [Pi2_04] at h; revert h; decide

end Refutations.WhiteFour
