/-
Refutation for the Laplace-domain part of `E:damped-multiplier-comparison` in
`L:damped-homogeneous-norms` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
826-847, and the kernel bounds at 888-889 and 903), package theorems
`StratonovichHAMSecondMoment.DampedNormsHomog.KS_le` and `KS_univ`
(restricting the Laplace domain decreases the kernel, `K_S(r) ≤ |r|^{-a}`).

Wrong variant: the reverse direction, `K_{S'}(r) ≤ K_S(r)` for `S ⊆ S'`.
Counterexample: `a = 1/2`, `r = 1`, `S = ∅`, `S' = (0,∞)` (all of `ℝ`):
`K_{S'}(1) = 1 > 0 = K_∅(1)`.  `kernel_direction_contrast` is the package
bound `K_∅(1) ≤ 1` at the same point.  No junk-value reliance (`r ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DampedNormsHomog

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedNormsHomog

namespace Refutations.DampedNormsHomog

/-- Enlarging the Laplace domain decreases the kernel: false. -/
theorem kernel_direction_refuted :
    ¬ (∀ S S' : Set ℝ, S ⊆ S' → KS (1 / 2) S' 1 ≤ KS (1 / 2) S 1) := by
  intro h
  have h1 := h ∅ univ (empty_subset _)
  rw [KS_univ _ _ (by norm_num) one_ne_zero] at h1
  simp [KS] at h1
  linarith

/-- The package bound at the same point: `K_∅(1) ≤ |1|^{-1/2}`. -/
theorem kernel_direction_contrast : KS (1 / 2) ∅ 1 ≤ |(1 : ℝ)| ^ (-(1 / 2 : ℝ)) :=
  (KS_le (1 / 2) ∅ 1 (by norm_num) one_ne_zero).2

end Refutations.DampedNormsHomog
