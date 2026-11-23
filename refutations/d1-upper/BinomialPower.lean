/-
Refutation for the binomial identity of the proof of `P:d1-upper` (main TeX
line 5515 at edf7085f): `Σ_{m=0}^{2k} 1/(m!(2k-m)!) = 2^{2k}/(2k)!`.  Package
theorem `StratonovichHAMSecondMoment.TwoSimplexTime.sum_inv_factorial_gen`
(moved from `D1Upper.sum_inv_factorial` at the L13 integration).

Wrong variant: `2^k/(2k)!` (the power that would lose the factor `2^k` in
`(2ZK_sp)^k`).  Counterexample in the manuscript domain: `k = 1`, where the sum
is `1/2 + 1 + 1/2 = 2` but `2^1/2! = 1`.  `binomialPower_contrast` is the
package identity.  Class (a): manuscript-claim perturbation in the manuscript
domain.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.D1Upper

set_option autoImplicit false

open StratonovichHAMSecondMoment D1Upper
open StratonovichHAMSecondMoment.TwoSimplexTime (sum_inv_factorial_gen)
open scoped Nat

namespace Refutations.D1Upper.BinomialPower

/-- The package: `Σ_{m=0}^{2k} 1/(m!(2k-m)!) = 2^{2k}/(2k)!`. -/
theorem binomialPower_contrast : ∀ k : ℕ,
    ∑ m ∈ Finset.range (2 * k + 1), (1 : ℝ) / ((m ! : ℝ) * ((2 * k - m) ! : ℝ)) =
      2 ^ (2 * k) / (2 * k) ! :=
  fun k => sum_inv_factorial_gen (2 * k)

/-- The power `2^k` in place of `2^{2k}` is false. -/
theorem binomialPower_refuted : ¬ (∀ k : ℕ,
    ∑ m ∈ Finset.range (2 * k + 1), (1 : ℝ) / ((m ! : ℝ) * ((2 * k - m) ! : ℝ)) =
      2 ^ k / (2 * k) !) := by
  intro H
  have h := (sum_inv_factorial_gen (2 * 1)).symm.trans (H 1)
  norm_num [Nat.factorial] at h

end Refutations.D1Upper.BinomialPower
