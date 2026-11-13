/-
Refutation for the tail bound of `L:uniform-series-tail`
(`notes/notes_stratonovich_ham_second_moment.tex` lines 3718-3723 and 3734-3736
at a284420), package theorem
`StratonovichHAMSecondMoment.UniformSeriesTail.tail_bound`.

Wrong variant: the tail bound without the geometric factor `1/(1 - r^{-1})`,
i.e. `‖Σ_{n>N} Z_n‖ ≤ c r^{-(N+1)}` whenever `‖Z_n‖ ≤ c r^{-n}`, `r > 1`.
Counterexample in `E = ℝ`: `Z_n = 2^{-n}`, `c = 1`, `r = 2`, `N = 0`: the tail
`Σ_{n≥1} 2^{-n} = 1 > 1/2`.  `tail_factor_contrast` is the package bound at the
same point: `1 ≤ (1/2)/(1 - 1/2) = 1`, with equality.
No junk-value reliance (`1 - r^{-1} = 1/2 ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.UniformSeriesTail

set_option autoImplicit false

open StratonovichHAMSecondMoment.UniformSeriesTail

namespace Refutations.UniformSeriesTail

theorem tsum_half_tail : ∑' n : ℕ, ((2 : ℝ) ^ (n + (0 + 1)))⁻¹ = 1 := by
  have h := (hasSum_geometric_tail 1 2 (by norm_num) 0).tsum_eq
  simp only [one_mul] at h
  rw [h]
  norm_num

/-- Dropping the factor `1/(1 - r^{-1})` from the tail bound is false. -/
theorem tail_factor_refuted :
    ¬ (∀ (Z : ℕ → ℝ) (c r : ℝ), 1 < r → (∀ n, ‖Z n‖ ≤ c * (r ^ n)⁻¹) →
        ∀ N : ℕ, ‖∑' n, Z (n + (N + 1))‖ ≤ c * (r ^ (N + 1))⁻¹) := by
  intro h
  have h1 := h (fun n => ((2 : ℝ) ^ n)⁻¹) 1 2 (by norm_num)
    (fun n => by simp) 0
  rw [tsum_half_tail] at h1
  norm_num at h1

/-- The package tail bound at the same point. -/
theorem tail_factor_contrast :
    ‖∑' n : ℕ, ((2 : ℝ) ^ (n + (0 + 1)))⁻¹‖ ≤
      1 * ((2 : ℝ) ^ (0 + 1))⁻¹ / (1 - (2 : ℝ)⁻¹) :=
  (tail_bound (fun n => ((2 : ℝ) ^ n)⁻¹) 1 2 (by norm_num) (fun n => by simp)).2 0

end Refutations.UniformSeriesTail
