/-
Refutation for the chain-root convention of `DiagramModel` (main TeX lines
811-813 at edf7085f: "at each first vertex set `(s_{p(l)}, y_{p(l)}) = (0,0)`.
Thus, the second chain has its own root, rather than the last vertex of the
first chain"), package definitions
`StratonovichHAMSecondMoment.DiagramModel.pred` and `twoSimplex`.

Wrong variant: the two chains form one ordered chain of length `m + n` (the
second chain continues from the last vertex of the first), so the time domain
is the single simplex `0 < s_1 < ⋯ < s_{m+n} < t` instead of
`[0,t]^m_< × [0,t]^n_<`.  Counterexample: `m = n = 1`, `t = 3`, the times
`(s_1, s_2) = (2, 1)`: they lie in `[0,3]^1_< × [0,3]^1_<` but not in the single
simplex; also the first label of the second chain has no predecessor.
`ownRoot_contrast` is the package membership at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramModel

set_option autoImplicit false

open StratonovichHAMSecondMoment DiagramModel

namespace Refutations.DiagramModel

/-- The single ordered simplex of one chain of length two. -/
def concatSimplex (t : ℝ) : Set (Fin 2 → ℝ) := {s | 0 < s 0 ∧ s 0 < s 1 ∧ s 1 < t}

/-- The package: `(2, 1)` lies in the two time simplices, and the second chain's
first label has no predecessor. -/
theorem ownRoot_contrast :
    (![2, 1] : Fin (1 + 1) → ℝ) ∈ twoSimplex 1 1 3 ∧ pred 1 (1 : Fin (1 + 1)) = none := by
  refine ⟨fun i => ?_, rfl⟩
  fin_cases i <;> norm_num [predVal, pred]

/-- The two time simplices are not the single simplex of the concatenated chain. -/
theorem ownRoot_refuted : ¬ (twoSimplex 1 1 3 = concatSimplex 3) := by
  intro h
  have h1 := ownRoot_contrast.1
  rw [h] at h1
  simp [concatSimplex] at h1

end Refutations.DiagramModel
