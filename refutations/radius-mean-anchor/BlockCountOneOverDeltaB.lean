/-
Refutation for the block count of `P:radius-mean-anchor` (TeX lines
320-321), package theorem
`StratonovichHAMSecondMoment.RadiusMeanAnchor.block_count_le`.

Wrong variant: the bound `N + 1 ≤ 2/(δB)` (N = ⌊1/(δB)⌋, δB < 1) sharpened to
`N + 1 ≤ 1/(δB)`, stated in the exact shape of `block_count_le` (same binders
`δ B : ℝ` and hypotheses `0 < δ`, `0 < B`, `δB < 1`). Witness: B = 1,
δ = 1/2; N = 2 and N + 1 = 3 > 2 = 1/(δB). The witness also satisfies the
earlier, more restrictive setting (B a positive integer, δ < min(1, 1/B)).
The contrast theorem applies `block_count_le` at the same point, where
`N + 1 = 3 ≤ 4 = 2/(δB)` holds.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RadiusMeanAnchor

set_option autoImplicit false

namespace Refutations.RadiusMeanAnchor

/-- The block count bound `N + 1 ≤ 2/(δB)` cannot be sharpened to
`N + 1 ≤ 1/(δB)`. -/
theorem block_count_one_over_deltaB :
    ¬ ∀ (δ B : ℝ), 0 < δ → 0 < B → δ * B < 1 →
      1 ≤ ⌊1 / (δ * B)⌋₊ ∧ ((⌊1 / (δ * B)⌋₊ : ℝ) + 1 ≤ 1 / (δ * B)) := by
  intro h
  have := (h (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)).2
  have hfl : ⌊(1 : ℝ) / (1 / 2 * 1)⌋₊ = 2 := by
    norm_num
  rw [hfl] at this
  norm_num at this

/-- Contrast: the package bound `block_count_le` holds at the witness
`δ = 1/2`, `B = 1`. -/
theorem block_count_one_over_deltaB_contrast :
    1 ≤ ⌊1 / ((1 / 2 : ℝ) * 1)⌋₊ ∧
      ((⌊1 / ((1 / 2 : ℝ) * 1)⌋₊ : ℝ) + 1 ≤ 2 / ((1 / 2 : ℝ) * 1)) :=
  StratonovichHAMSecondMoment.RadiusMeanAnchor.block_count_le (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num)

end Refutations.RadiusMeanAnchor
