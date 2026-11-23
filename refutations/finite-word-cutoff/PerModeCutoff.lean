/-
Refutation for the form of the cutoff in the multi-mode `L:finite-word-cutoff`
(main TeX lines 3036-3058 at edf7085f: "`P` projects each color onto total Hermite
degree at most `N_i`", line 3046-3047; the cutoff `P = ⊗_i P_{N_i}` of
`L:fixed-split`, lines 3680-3682), package definitions
`StratonovichHAMSecondMoment.FixedSplit.cutIdx` and
`StratonovichHAMSecondMoment.FiniteWordCutoff.truncN`.

Wrong variant: the color total-degree cutoff is the per-mode cutoff
`k_j ≤ N_{col j}` (the cutoff of `HermiteWordFock.cut_eq_raw_fock`, one mode per
color), so that the per-coordinate lemma would apply directly.  Counterexample: two
modes of one color, `N = 1`, the multi-index `(1, 1)`: each mode has degree `1 ≤ 1`,
but the color total degree is `2 > 1`.  `per_mode_cutoff_contrast` is the true
inclusion (color total cutoff inside the per-mode box).  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FiniteWordCutoff

set_option autoImplicit false

namespace Refutations.FiniteWordCutoff.PerMode

open StratonovichHAMSecondMoment.FixedSplit

/-- The color total-degree cutoff is not the per-mode cutoff. -/
theorem per_mode_cutoff_refuted :
    ¬ (∀ (m : ℕ) (col : Fin m → Unit) (N : Unit → ℕ) (k : Fin m → ℕ),
        k ∈ cutIdx col N ↔ ∀ j, k j ≤ N (col j)) := by
  intro hall
  have h := (hall 2 (fun _ => ()) (fun _ => 1) (fun _ => 1)).2 (fun _ => le_rfl)
  rw [mem_cutIdx] at h
  have h1 := h ()
  simp [colorDeg] at h1

/-- The true inclusion: the color total-degree cutoff lies in the per-mode box. -/
theorem per_mode_cutoff_contrast {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (col : Fin m → ι) (N : ι → ℕ) (k : Fin m → ℕ) (hk : k ∈ cutIdx col N) :
    ∀ j, k j ≤ N (col j) := fun j =>
  (le_colorDeg col k j).trans ((mem_cutIdx col N k).1 hk (col j))

end Refutations.FiniteWordCutoff.PerMode
