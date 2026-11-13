/-
Refutation for the pairing-sum bound of `FiniteWick` (behind the moment bound
of `L:terminal-wick`, main TeX lines 3651-3656 at a284420), package theorem
`StratonovichHAMSecondMoment.FiniteWick.wickSum_abs_le`.

Wrong variant: `|Σ_D ∏ c| ≤ V^k` for a `2k`-set when `|c| ≤ V` (dropping the
factor `(2k-1)!!`, the number of pairings).  Counterexample: `c ≡ 1`, `V = 1`,
the set `Fin 4` (`k = 2`): the pairing sum is the number of pairings, `3 > 1`.
`abs_bound_contrast` is the package bound at the same point: `|3| ≤ 3!! · 1 = 3`.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FiniteWick

set_option autoImplicit false

open StratonovichHAMSecondMoment FiniteWick

namespace Refutations.FiniteWick

/-- With all weights `1`, the pairing sum over `Fin 4` is `3`. -/
theorem wickSum_one_fin_four :
    wickSum (fun _ _ : Fin 4 => (1 : ℝ)) Finset.univ = 3 := by
  rw [wickSum_const_one, card_pairings_even 2 _ (by simp)]
  norm_num [Nat.doubleFactorial]

/-- The package bound at the counterexample. -/
theorem abs_bound_contrast :
    |wickSum (fun _ _ : Fin 4 => (1 : ℝ)) Finset.univ| ≤
      ((2 * 2 - 1).doubleFactorial : ℝ) * 1 ^ 2 :=
  wickSum_abs_le _ 1 (fun _ _ => by simp) 2 _ (by simp)

/-- The bound without the factor `(2k-1)!!` is false. -/
theorem abs_bound_refuted :
    ¬ (∀ (k : ℕ) (c : Fin (2 * k) → Fin (2 * k) → ℝ) (V : ℝ), (∀ x y, |c x y| ≤ V) →
        |wickSum c Finset.univ| ≤ V ^ k) := by
  intro h
  have h2 := h 2 (fun _ _ => 1) 1 (fun _ _ => by simp)
  rw [wickSum_one_fin_four] at h2
  norm_num at h2

end Refutations.FiniteWick
