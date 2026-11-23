/-
Refutation for `E:split-explicit-constant` (main TeX lines 4037-4038 at
edf7085f), package theorem
`StratonovichHAMSecondMoment.FixedSplitCore.Mk_sq_le`
(`M_k² ≤ (100^8 e^8)^k` for `k ≥ 1`).

Wrong variant: the smaller base `100^7 e^8`, i.e. `M_k² ≤ (100^7 e^8)^k` for
every `k ≥ 1`.  Counterexample: `k = 1`, where `M_1² = 100^8 e^8`.
`mk_square_contrast` is the package bound at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FixedSplitCore

set_option autoImplicit false

namespace Refutations.FixedSplitCore

open StratonovichHAMSecondMoment.FixedSplitCore

/-- The base `100^7 e^8` in `M_k² ≤ (·)^k` is false. -/
theorem mk_square_constant_refuted :
    ¬ (∀ k : ℕ, 1 ≤ k → Mk k ^ 2 ≤ (100 ^ 7 * Real.exp 8) ^ k) := by
  intro h
  have h1 := h 1 le_rfl
  have hval : Mk 1 ^ 2 = 100 ^ 8 * Real.exp 8 := by
    unfold Mk
    rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    norm_num
  rw [hval, pow_one] at h1
  have he := Real.exp_pos 8
  nlinarith

/-- The package bound at the same point `k = 1`. -/
theorem mk_square_contrast : Mk 1 ^ 2 ≤ (100 ^ 8 * Real.exp 8) ^ 1 :=
  Mk_sq_le 1 le_rfl

end Refutations.FixedSplitCore
