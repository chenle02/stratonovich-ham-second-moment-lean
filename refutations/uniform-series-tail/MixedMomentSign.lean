/-
Refutation for the term bound of `L:uniform-series-tail`
(`notes/notes_stratonovich_ham_second_moment.tex` lines 3703-3733 at a284420),
package theorem `StratonovichHAMSecondMoment.UniformSeriesTail.term_bound`.

Wrong variant: the term bound `‖Y_n‖ ≤ B^{1/2} r^{-n}` without the
`L:terminal-wick` input of nonnegative mixed moments `⟪Y_m, Y_n⟫ ≥ 0`.
Counterexample in `E = ℝ`: `r = 2`, `Y_0 = 1`, `Y_1 = -1`, `Y_n = 0` otherwise;
then `Σ r^n Y_n = 1 - 2 = -1`, so `B = 1` bounds its square, but
`‖Y_1‖ = 1 > 1/2 = B^{1/2} r^{-1}`.  The mixed moment `⟪Y_0, Y_1⟫ = -1 < 0`.
`mixed_moment_sign_contrast` applies the package theorem to `Y_0 = Y_1 = 1`
(`Σ 2^n Y_n = 3`, `B = 9`), where `‖Y_1‖ = 1 ≤ 3/2`.
No junk-value reliance (`B ≥ 0`, `r > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.UniformSeriesTail

set_option autoImplicit false

open StratonovichHAMSecondMoment.UniformSeriesTail

namespace Refutations.UniformSeriesTail

/-- Auxiliary sequence supported on `{0, 1}`. -/
noncomputable def two (a b : ℝ) : ℕ → ℝ := fun n => if n = 0 then a else if n = 1 then b else 0

theorem tsum_two_mul (a b r : ℝ) :
    ∑' n, r ^ n • two a b n = a + r * b := by
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [two]
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [two, hn.1, hn.2]

theorem summable_two_mul (a b r : ℝ) : Summable fun n => ‖r ^ n • two a b n‖ := by
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [two, hn.1, hn.2]

/-- Without nonnegative mixed moments the term bound is false. -/
theorem mixed_moment_sign_refuted :
    ¬ (∀ (Y : ℕ → ℝ) (r B : ℝ), 0 < r →
        (Summable fun n => ‖r ^ n • Y n‖) →
        ‖∑' n, r ^ n • Y n‖ ^ 2 ≤ B →
        ∀ n, ‖Y n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) := by
  intro h
  have h1 := h (two 1 (-1)) 2 1 (by norm_num) (summable_two_mul _ _ _)
    (by rw [tsum_two_mul]; norm_num) 1
  simp [two] at h1
  norm_num at h1

/-- The package bound at the nonnegative example `Y_0 = Y_1 = 1`, `r = 2`, `B = 9`. -/
theorem mixed_moment_sign_contrast : ‖two 1 1 1‖ ≤ Real.sqrt 9 * ((2 : ℝ) ^ 1)⁻¹ := by
  refine term_bound (two 1 1) 2 9 (by norm_num) (summable_two_mul _ _ _) ?_ ?_ 1
  · intro m n
    simp only [two]
    split_ifs <;> simp
  · rw [tsum_two_mul]; norm_num

end Refutations.UniformSeriesTail
