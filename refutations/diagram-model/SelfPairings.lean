/-
Refutation for the self-pairing convention of `DiagramModel` (`Π_k` of
`E:mixed-diagram` and `E:mixed-moment`, main TeX lines 808-810 at 39f2597a: "A
self-pairing has both endpoints in one chain; a cross-pairing has one endpoint
in each chain. Both are included in `Π_k`."), package definition
`StratonovichHAMSecondMoment.DiagramModel.Pi2` and theorem `card_Pi2_two_zero`.

Wrong variant: `Π_k` consists of the cross-pairings only (the Skorohod-type
pairing set, without self-pairings).  Counterexample: `m = 2`, `n = 0` (the
diagram of `E X_2` in `L:white-test`): there is exactly one pairing, the
self-pairing of the two labels of the first chain, and no cross-pairing; the
cross-only reading would make `E X_2 = 0`, against `E:white-test`.
`selfPairings_contrast` is the package count at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance (finite sets only).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramModel

set_option autoImplicit false

open StratonovichHAMSecondMoment DiagramModel

namespace Refutations.DiagramModel

/-- The package count: `Π` for `m = 2`, `n = 0` has one element. -/
theorem selfPairings_contrast : (Pi2 2 0).card = 1 := card_Pi2_two_zero

/-- `Π_k` is not the set of cross-pairings. -/
theorem selfPairings_omitted_refuted : ¬ (crossPairs 2 0 = Pi2 2 0) := by
  intro h
  have h1 := selfPairings_contrast
  rw [← h, crossPairs_two_zero] at h1
  simp at h1

end Refutations.DiagramModel
