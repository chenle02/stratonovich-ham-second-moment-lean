/-
Refutation for the tail bound used in the proof of `L:inventory-product`
(`notes/notes_stratonovich_ham_second_moment.tex` lines 3024-3035 at a284420),
package theorem `StratonovichHAMSecondMoment.InventoryProduct.sum_rpow_tail_le`
(`∑_{i ∈ t, i > a} i^{-s} ≤ a^{1-s}/(s-1)`).

Wrong variant: the denominator `s` in place of `s - 1`, i.e.
`∑_{i ∈ t} i^{-s} ≤ a^{1-s}/s`. Counterexample: `s = 2`, `a = 1`,
`t = {2, …, 7}`: `∑ i^{-2} = 1/4 + 1/9 + 1/16 + 1/25 + 1/36 + 1/49 > 1/2`.
`tail_constant_contrast` is the package bound at the same point (`≤ 1`).
No junk-value reliance (`a = 1`, all bases positive).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.InventoryProduct

set_option autoImplicit false

open Finset
open StratonovichHAMSecondMoment.InventoryProduct

namespace Refutations.InventoryProduct

theorem tail_sum_value :
    ∑ i ∈ (Icc 2 7 : Finset ℕ), (i : ℝ) ^ (-(2 : ℝ)) =
      1 / 4 + 1 / 9 + 1 / 16 + 1 / 25 + 1 / 36 + 1 / 49 := by
  rw [show (Icc 2 7 : Finset ℕ) = ({2, 3, 4, 5, 6, 7} : Finset ℕ) by decide]
  simp [Finset.sum_insert]
  norm_num

/-- The tail bound with denominator `s` instead of `s - 1` is false. -/
theorem tail_constant_refuted :
    ¬ (∀ s : ℝ, 1 < s → ∀ a : ℕ, 1 ≤ a → ∀ t : Finset ℕ, (∀ i ∈ t, a < i) →
        ∑ i ∈ t, (i : ℝ) ^ (-s) ≤ (a : ℝ) ^ (1 - s) / s) := by
  intro h
  have := h 2 (by norm_num) 1 le_rfl ((Icc 2 7 : Finset ℕ)) (fun i hi => by
    rw [mem_Icc] at hi; omega)
  rw [tail_sum_value] at this
  norm_num at this

/-- The package bound at the same point. -/
theorem tail_constant_contrast :
    ∑ i ∈ (Icc 2 7 : Finset ℕ), (i : ℝ) ^ (-(2 : ℝ)) ≤ ((1 : ℕ) : ℝ) ^ (1 - (2 : ℝ)) / (2 - 1) :=
  sum_rpow_tail_le (by norm_num) le_rfl _ fun i hi => by rw [mem_Icc] at hi; omega

end Refutations.InventoryProduct
