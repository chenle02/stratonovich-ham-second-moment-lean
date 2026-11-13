/-
Refutation for the term bound of `L:uniform-series-tail`
(`notes/notes_stratonovich_ham_second_moment.tex` lines 3718-3720 and 3730-3733
at a284420), package theorem
`StratonovichHAMSecondMoment.UniformSeriesTail.term_bound`.

Wrong variant: the exponent `r^{-n}` replaced by `r^{-2n}` (the square of the
true rate), i.e. `‖Y_n‖ ≤ B^{1/2} r^{-2n}`.  Counterexample in `E = ℝ`:
`r = 2`, `Y_1 = 1`, `Y_n = 0` otherwise (all mixed moments are `≥ 0`); then
`Σ r^n Y_n = 2`, `B = 4`, and `‖Y_1‖ = 1 > 2 · 2^{-2} = 1/2`.
`term_exponent_contrast` is the package bound at the same point:
`1 ≤ 2 · 2^{-1} = 1`, with equality (so `r^{-n}` is attained).
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.UniformSeriesTail

set_option autoImplicit false

open StratonovichHAMSecondMoment.UniformSeriesTail

namespace Refutations.UniformSeriesTail

/-- Auxiliary sequence `e_1`. -/
noncomputable def e1 : ℕ → ℝ := fun n => if n = 1 then 1 else 0

theorem tsum_e1 (r : ℝ) : ∑' n, r ^ n • e1 n = r := by
  rw [tsum_eq_single 1]
  · simp [e1]
  · intro n hn; simp [e1, hn]

theorem summable_e1 (r : ℝ) : Summable fun n => ‖r ^ n • e1 n‖ := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [e1, hn]

theorem e1_inner_nonneg (m n : ℕ) : 0 ≤ inner ℝ (e1 m) (e1 n) := by
  simp only [e1]
  split_ifs <;> simp

/-- The rate `r^{-2n}` in the term bound is false. -/
theorem term_exponent_refuted :
    ¬ (∀ (Y : ℕ → ℝ) (r B : ℝ), 0 < r →
        (Summable fun n => ‖r ^ n • Y n‖) →
        (∀ m n, 0 ≤ inner ℝ (Y m) (Y n)) →
        ‖∑' n, r ^ n • Y n‖ ^ 2 ≤ B →
        ∀ n, ‖Y n‖ ≤ Real.sqrt B * (r ^ (2 * n))⁻¹) := by
  intro h
  have h1 := h e1 2 4 (by norm_num) (summable_e1 _) e1_inner_nonneg
    (by rw [tsum_e1]; norm_num) 1
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [e1, hs] at h1
  norm_num at h1

/-- The package bound at the same point. -/
theorem term_exponent_contrast : ‖e1 1‖ ≤ Real.sqrt 4 * ((2 : ℝ) ^ 1)⁻¹ :=
  term_bound e1 2 4 (by norm_num) (summable_e1 _) e1_inner_nonneg
    (by rw [tsum_e1]; norm_num) 1

end Refutations.UniformSeriesTail
