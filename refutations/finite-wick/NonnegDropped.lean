/-
Refutation for the nonnegativity of pairing sums (`L:terminal-wick`, main TeX
lines 3639-3640 and 3693-3694 at a284420: "if `K ≥ 0`, every integral above is
nonnegative"), package theorem
`StratonovichHAMSecondMoment.FiniteWick.wickSum_nonneg`.

Wrong variant: the hypothesis `c ≥ 0` dropped, i.e. every pairing sum is
nonnegative.  Counterexample: `c ≡ -1` on the set `Fin 2`: the only pairing
`{0,1}` gives `-1`.  `nonneg_contrast` is the package theorem with `c ≡ 1`
at the same set.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FiniteWick

set_option autoImplicit false

open StratonovichHAMSecondMoment FiniteWick

namespace Refutations.FiniteWick

/-- With all weights `-1`, the pairing sum over `Fin 2` is `-1`. -/
theorem wickSum_neg_one_fin_two :
    wickSum (fun _ _ : Fin 2 => (-1 : ℝ)) Finset.univ = -1 := by
  rw [wickSum_eq_sum_erase _ _ 0 (Finset.mem_univ 0) (fun x _ => Fin.zero_le x)]
  have h1 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h2 : ({1} : Finset (Fin 2)).erase 1 = ∅ := by decide
  rw [h1, Finset.sum_singleton, h2, wickSum_empty]
  norm_num

/-- The package theorem with nonnegative weights at the same set. -/
theorem nonneg_contrast : 0 ≤ wickSum (fun _ _ : Fin 2 => (1 : ℝ)) Finset.univ :=
  wickSum_nonneg _ (fun _ _ => zero_le_one) _

/-- Nonnegativity without `c ≥ 0` is false. -/
theorem nonneg_dropped_refuted :
    ¬ (∀ c : Fin 2 → Fin 2 → ℝ, 0 ≤ wickSum c Finset.univ) := by
  intro h
  have := h fun _ _ => -1
  rw [wickSum_neg_one_fin_two] at this
  norm_num at this

end Refutations.FiniteWick
