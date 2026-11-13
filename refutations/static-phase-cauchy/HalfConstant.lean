import StratonovichHAMSecondMoment.StaticPhaseCauchy

/-!
Refutation for `StratonovichHAMSecondMoment.StaticPhaseCauchy.all_orders_arith` (the
scalar arithmetic of `P:static-phase-all-orders`, main TeX lines 2631-2641 at a284420).

Wrong variant: the constant `A = 400 √2 e²/δ` of `E:all-static-phase-orders` replaced by
a quarter of it, `100 √2 e²/δ` (the factor `100 n ≤ 200^n` of line 2640 dropped).
Counterexample: `n = 1`, `h = δ = R = 1`, `α = 1`, `d = 2√2`, where the left side is
`200 √2 e²` and the wrong right side is `100 √2 e²`.  No junk-value reliance (all
bases positive).  `half_constant_contrast` is the package inequality at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open Real
open scoped Nat

namespace Refutations.StaticPhaseCauchy

open StratonovichHAMSecondMoment.StaticPhaseCauchy

/-- The arithmetic step fails with the constant `100 √2 e²/δ`. -/
theorem half_constant_refuted :
    ¬ (∀ (n : ℕ), 1 ≤ n → ∀ h R δ alpha d : ℝ, 0 < h → 0 < δ → alpha ≤ 3 → 0 ≤ d →
        d ≤ 2 * √(2 * n) * √R →
        n * (100 * Real.exp (2 * (n / h) * h) * (d / (δ * (n / h) ^ (2 - alpha / 2))) ^ n) ≤
          (100 * √2 * Real.exp 2 / δ * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
            (n ! : ℝ) ^ ((3 - alpha) / 2)) := by
  intro H
  have h1 := H 1 le_rfl 1 1 1 1 (2 * √2) one_pos one_pos (by norm_num) (by positivity)
    (by norm_num)
  norm_num at h1
  have he : 0 < Real.exp 2 := Real.exp_pos 2
  have hs : 0 < √2 := by positivity
  nlinarith [mul_pos he hs]

/-- Contrast: the package inequality (constant `400 √2 e²/δ`) at the same point. -/
theorem half_constant_contrast :
    (1 : ℕ) * (100 * Real.exp (2 * ((1 : ℕ) / (1 : ℝ)) * 1) *
        (2 * √2 / (1 * ((1 : ℕ) / (1 : ℝ)) ^ (2 - (1 : ℝ) / 2))) ^ 1) ≤
      (orderConst 1 * √1) ^ 1 * (1 : ℝ) ^ ((4 - (1 : ℝ)) * (1 : ℕ) / 2) /
        ((1 : ℕ)! : ℝ) ^ ((3 - (1 : ℝ)) / 2) :=
  all_orders_arith le_rfl one_pos one_pos (by norm_num) (by positivity) (by norm_num)

end Refutations.StaticPhaseCauchy
