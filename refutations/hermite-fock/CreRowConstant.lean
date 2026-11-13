import StratonovichHAMSecondMoment.HermiteFock

/-!
Refutation for `StratonovichHAMSecondMoment.HermiteFock.creRow_bound` (the creation row from
degrees `≤ N` to `≤ N+1` has norm `√(N+1)`, main TeX lines 2517-2519 at a284420).

Wrong variant: the constant `N` in place of `N+1`.  Counterexample: `N = 0`, `X = ℂ`, one mode,
`u_0 = 1 ⊗ 1` (the vacuum): `a_0^* u_0` has norm `1`, the wrong bound is `0`.
No junk-value reliance.  `cre_row_contrast` is the package bound at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.HermiteFock

open StratonovichHAMSecondMoment.HermiteFock StratonovichHAMSecondMoment.GaussianHermite

/-- The creation-row bound fails with constant `N` (here `N = 0`). -/
theorem cre_row_constant_refuted :
    ¬ (∀ u : Fin 1 → (Fin 1 → ℕ) → ℂ,
        ∑ k ∈ degLE 1 (0 + 1), ‖creRow u k‖ ^ 2 ≤
          ((0 : ℕ) : ℝ) * ∑ i, ∑ j ∈ degLE 1 0, ‖u i j‖ ^ 2) := by
  intro H
  have h := H (fun _ => vac 1)
  have hmem : unitIdx (0 : Fin 1) ∈ degLE 1 (0 + 1) := mem_degLE.2 (by simp [deg, unitIdx])
  have hterm : ‖creRow (fun _ => vac (1 : ℂ)) (unitIdx (0 : Fin 1))‖ ^ 2 = 1 := by
    simp [creRow, cre, vac, unitIdx]
  have hle := Finset.single_le_sum (f := fun k => ‖creRow (fun _ => vac (1 : ℂ)) k‖ ^ 2)
    (fun k _ => sq_nonneg _) hmem
  rw [hterm] at hle
  norm_num at h
  linarith

/-- Contrast: the package bound (constant `N + 1 = 1`) at the same point. -/
theorem cre_row_contrast :
    ∑ k ∈ degLE 1 (0 + 1), ‖creRow (fun _ : Fin 1 => vac (1 : ℂ)) k‖ ^ 2 ≤
      ((0 : ℕ) + 1 : ℝ) * ∑ _i : Fin 1, ∑ j ∈ degLE 1 0, ‖vac (m := 1) (1 : ℂ) j‖ ^ 2 :=
  creRow_bound 0 _

end Refutations.HermiteFock
