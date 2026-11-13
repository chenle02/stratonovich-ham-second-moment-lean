/-
Refutation for the abstract compact-perturbation bound
`StratonovichHAMSecondMoment.SymplecticFree.norm_le_norm_add_compact`
(`‖S‖ ≤ ‖S + K‖` for compact `K`; `L:symplectic-free`,
`notes/integrated_symplectic_phase.tex` lines 103-119 at a284420).

Wrong variant: the bound without the weakly null isometries commuting with `S`.
Counterexample: on `ℝ`, `S = I` and the compact `K = -I` (finite rank) give
`‖S + K‖ = 0 < 1 = ‖S‖`.  No contrast theorem: on `ℝ` there is no family of
isometries that is weakly null along a nontrivial filter (every isometry is `±I`), so
the package hypotheses cannot be met there; that hypothesis is what the
counterexample shows to be needed.
Junk-value reliance: none.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SymplecticFree

set_option autoImplicit false

namespace Refutations.SymplecticFree

open Filter Topology

/-- Auxiliary: `-I` is compact on `ℝ`. -/
theorem neg_one_isCompactOperator : IsCompactOperator (⇑(-1 : ℝ →L[ℝ] ℝ)) := by
  refine ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, ?_⟩
  have : (⇑(-1 : ℝ →L[ℝ] ℝ)) ⁻¹' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
    ext x; simp
  rw [this]
  exact Metric.closedBall_mem_nhds 0 one_pos

/-- `‖S‖ ≤ ‖S + K‖` fails for general compact `K` without weakly null translations. -/
theorem weak_nullity_refuted :
    ¬ (∀ S K : ℝ →L[ℝ] ℝ, IsCompactOperator (⇑K) → ‖S‖ ≤ ‖S + K‖) := by
  intro h
  have := h 1 (-1) neg_one_isCompactOperator
  norm_num at this

end Refutations.SymplecticFree
