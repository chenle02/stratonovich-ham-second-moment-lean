/-
Refutation for the chain-orientation step of `DiagramModel` (proof of `P:mixed`,
main TeX lines 883-903 at edf7085f: reversing both terminal chains by the vertex
involution `ρ` "induces the pairing bijection
`D ↦ {{ρ(a), ρ(b)} : {a,b} ∈ D}`"), package definitions
`StratonovichHAMSecondMoment.DiagramModel.rev`, `revPairing` and theorem
`revPairing_mem`.

Wrong variant: reversing the chain orientation leaves the pairing unchanged
(`ρ(D) = D` for every `D ∈ Π_k`), so the terminal-chain diagram with `D` could
be read as the initial-chain diagram `J_{m,n,D}` with the same `D`.
Counterexample: `m = 3`, `n = 1`, `D = {{1,2},{3,4}}` (0-based `{{0,1},{2,3}}`):
`ρ(D) = {{1,4},{2,3}}`, which differs from `D`; in particular the opening labels
(the set `O_D` of `L:d1-spatial`) change from `{1,3}` to `{1,2}`.
`orientation_contrast` is the package fact that `ρ(D)` is again a pairing.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramModel

set_option autoImplicit false

open StratonovichHAMSecondMoment DiagramModel

namespace Refutations.DiagramModel

/-- The pairing `{{0,1},{2,3}}` of the labels of chains of lengths `3` and `1`. -/
def adjPairing : Fin (3 + 1) → Fin (3 + 1) := ![1, 0, 3, 2]

theorem adjPairing_mem : adjPairing ∈ Pi2 3 1 := by
  rw [mem_Pi2]; decide

/-- The package: `ρ(D)` is a pairing. -/
theorem orientation_contrast : revPairing 3 1 adjPairing ∈ Pi2 3 1 :=
  revPairing_mem adjPairing_mem

/-- Chain reversal changes the pairing. -/
theorem orientation_refuted :
    ¬ (∀ D ∈ Pi2 3 1, revPairing 3 1 D = D) := by
  intro h
  have h1 := congrFun (h adjPairing adjPairing_mem) 0
  revert h1
  decide

/-- Chain reversal changes the opening labels. -/
theorem openers_refuted : ¬ (openers (revPairing 3 1 adjPairing) = openers adjPairing) := by
  decide

end Refutations.DiagramModel
