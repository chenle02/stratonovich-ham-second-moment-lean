/-
Refutation for the per-frequency identity
`StratonovichHAMSecondMoment.SymplecticFree.freeMatrix_symplectic`
(`W_tᵀ J_symp W_t = J_symp`; `L:symplectic-free`,
`notes/integrated_symplectic_phase.tex` lines 79-81 at a284420).

Wrong variant: the free matrix is orthogonal, `W_tᵀ W_t = I` (the free group would then
be isometric and `‖S_E(h)‖ ≥ 1` would be an equality).  Counterexample: `t = 1`,
`k = 0`, `⟨ξ⟩ = 1`, where `W = (1 1; 0 1)` and `Wᵀ W = (1 1; 1 2)`.
`not_orthogonal_contrast` is the package identity at the same point.
Junk-value reliance: none (`k = 0` uses the continuous sine quotient).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SymplecticFree

set_option autoImplicit false

namespace Refutations.SymplecticFree

open StratonovichHAMSecondMoment.SymplecticFree Matrix

/-- The free matrix is not orthogonal in general. -/
theorem not_orthogonal_refuted :
    ¬ (∀ t k br : ℝ, br ≠ 0 → (freeMatrix t k br)ᵀ * freeMatrix t k br = 1) := by
  intro h
  have := congrFun (congrFun (h 1 0 1 one_ne_zero) 1) 1
  rw [freeMatrix_zero_freq] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

/-- The package identity at the same point: the matrix is symplectic. -/
theorem not_orthogonal_contrast :
    (freeMatrix 1 0 1)ᵀ * Jsymp * freeMatrix 1 0 1 = Jsymp :=
  freeMatrix_symplectic 1 0 one_ne_zero

end Refutations.SymplecticFree
