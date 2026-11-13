/-
Refutation for the scalar identity of `SpatialFourierBound`, package theorem
`StratonovichHAMSecondMoment.SpatialFourierBound.scalar_identity`
(`8 b (2√b)^{α-2} = 2^{1+α} b^{α/2}`; auxiliary to the Lean proof route of the
deterministic bound `A_sp(g) ≤ 2^{1+α} R_Γ(1) b^{α/2}` for
`P:spatial-smooth-ratio`, `notes/integrated_spatial_occupation.tex` lines
166-170 at a284420).

Wrong variant: the constant `2^α` instead of `2^{1+α}`, i.e.
`8 b (2√b)^{α-2} = 2^α b^{α/2}` for all `α` and `b > 0`.
Counterexample: `α = 1`, `b = 1`: the left side is `8 · 2^{-1} = 4`, the
variant's right side is `2`.  `scalar_exponent_contrast` is the package identity
at the same point (`4 = 2^2`).
No junk-value reliance (`b > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialFourierBound

set_option autoImplicit false

open StratonovichHAMSecondMoment SpatialFourierBound

namespace Refutations.SpatialFourierBound

/-- Auxiliary: the left side at `α = 1`, `b = 1`. -/
theorem lhs_value : 8 * (1 : ℝ) * (2 * Real.sqrt 1) ^ ((1 : ℝ) - 2) = 4 := by
  rw [Real.sqrt_one, mul_one, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-- The constant `2^α` in the scalar identity is false. -/
theorem scalar_exponent_refuted :
    ¬ (∀ alpha b : ℝ, 0 < b → 8 * b * (2 * Real.sqrt b) ^ (alpha - 2) =
        2 ^ alpha * b ^ (alpha / 2)) := by
  intro h
  have h1 := h 1 1 one_pos
  rw [lhs_value, Real.one_rpow, Real.rpow_one] at h1
  norm_num at h1

/-- The package identity at the same point: `4 = 2^{1+1} · 1`. -/
theorem scalar_exponent_contrast :
    8 * (1 : ℝ) * (2 * Real.sqrt 1) ^ ((1 : ℝ) - 2) = 2 ^ ((1 : ℝ) + 1) * 1 ^ ((1 : ℝ) / 2) :=
  scalar_identity 1 1 one_pos

end Refutations.SpatialFourierBound
