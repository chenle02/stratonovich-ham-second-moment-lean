/-
Refutation for the separate chain roots in the positions/increments change of
variables of `DiagramBridge` (main TeX lines 811-813 and 5339-5341 at edf7085f:
"with a separate root zero in each chain.  Thus, `x_l` is the sum of
increments in its own chain up to label `l`"), package definitions
`StratonovichHAMSecondMoment.DiagramBridge.incrOfPos` and
`StratonovichHAMSecondMoment.DiagramModel.pos`, theorem `incrOfPos_pos`.

Wrong variant: the increments taken with the global predecessor (the two chains
concatenated, so the first vertex of the second chain is measured from the last
vertex of the first chain).  Counterexample: `m = n = 1`, `w = (v, v)` with
`v = e_0 ≠ 0`: the positions are `(v, v)` (two roots), whose global increments
are `(v, 0) ≠ w`.  `globalPredecessor_contrast` is the package inversion at the
same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramBridge

set_option autoImplicit false

open StratonovichHAMSecondMoment DiagramModel DiagramBridge

namespace Refutations.DiagramBridge

/-- The increments with the global predecessor of the concatenated chain. -/
def globalIncr (y : Fin (1 + 1) → HomogHypothesis.Rd 1) : Fin (1 + 1) → HomogHypothesis.Rd 1 :=
  ![y 0, y 1 - y 0]

/-- The counterexample increments `(e_0, e_0)`. -/
noncomputable def wGP : Fin (1 + 1) → HomogHypothesis.Rd 1 := fun _ => EuclideanSpace.single 0 1

/-- The package: the own-chain increments of the positions are the increments. -/
theorem globalPredecessor_contrast : incrOfPos 1 (pos 1 wGP) = wGP :=
  incrOfPos_pos 1 wGP

/-- The global-predecessor increments of the positions are not the increments. -/
theorem globalPredecessor_refuted : ¬ (globalIncr (pos 1 wGP) = wGP) := by
  intro h
  have hp : ∀ i, pos 1 wGP i = wGP i := fun i => by
    rw [pos_eq_add_predVal, predVal_of_none]
    · rw [add_zero]
    · fin_cases i <;> rfl
  have h1 := congrFun h 1
  simp only [globalIncr, Matrix.cons_val_one, Matrix.cons_val_zero, hp] at h1
  have h2 := congrArg (fun x : HomogHypothesis.Rd 1 => x 0) h1
  simp [wGP] at h2

end Refutations.DiagramBridge
