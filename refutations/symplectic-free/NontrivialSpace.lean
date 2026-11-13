/-
Refutation for `StratonovichHAMSecondMoment.SymplecticFree.one_le_norm_of_reversal`
(`‖S_E(h)‖ ≥ 1` from the group law and the isometric reversal; `L:symplectic-free`,
`notes/integrated_symplectic_phase.tex` lines 120-122 at a284420).

Wrong variant: the bound without `Nontrivial E`.  Counterexample: the zero space
`EuclideanSpace ℝ (Fin 0)`, where `A = B = R = 0` satisfy `B A = 1`, `R` isometric and
`B = R A R`, but `‖A‖ = 0`.  `nontrivial_space_contrast` is the package bound on `ℝ`
with `A = B = R = 1`.
Junk-value reliance: none (the zero space is a genuine normed space; the failure is
that every operator on it has norm `0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SymplecticFree

set_option autoImplicit false

namespace Refutations.SymplecticFree

/-- `‖A‖ ≥ 1` fails on the zero space: `Nontrivial E` cannot be dropped. -/
theorem nontrivial_space_refuted :
    ¬ (∀ A B R : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0),
        B * A = 1 → (∀ z, ‖R z‖ = ‖z‖) → B = R * A * R → 1 ≤ ‖A‖) := by
  intro h
  have hsub : ∀ T : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0), T = 0 := by
    intro T; ext z i; exact i.elim0
  have := h 0 0 0 (by rw [hsub (0 * 0), hsub 1]) (fun z => by simp [Subsingleton.elim z 0])
    (by simp)
  norm_num at this

/-- The package bound on `ℝ` at `A = B = R = 1`. -/
theorem nontrivial_space_contrast : 1 ≤ ‖(1 : ℝ →L[ℝ] ℝ)‖ :=
  StratonovichHAMSecondMoment.SymplecticFree.one_le_norm_of_reversal 1 1 1 (by simp)
    (fun z => by simp) (by simp)

end Refutations.SymplecticFree
