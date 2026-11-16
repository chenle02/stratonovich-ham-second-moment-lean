/-
Refutation for the partial-sum comparison of `L:terminal-wick` (main TeX lines 4331-4333, proof
4404-4406 at 39f2597a), package theorem
`StratonovichHAMSecondMoment.TerminalWickComplete.norm_sq_partial_le` (used by
`partial_sum_mono_constructed_paper` and `terminal_wick_full_constructed_paper`).

Wrong variant: the same comparison for COMPLEX `r`, `|Σ_{n∈s} r^n Y_n|² ≤ |Σ_{n∈s} r^n Y'_n|²`,
from the same hypotheses (entrywise comparison of the Gram entries, odd entries zero).  The TeX
does not state it (it states only the convergence for complex `r`); this control shows why the
Lean wrapper restricts the comparison to real `r`: `r^m conj(r)^n` is not nonnegative for even
`m + n`.  Counterexample in `ℝ`: `Y = (1, 0, 0)`, `Y' = (1, 0, 1)`, `r = i`, `s = {0,1,2}`:
`|1|² = 1` but `|1 + i²|² = 0`.  `complex_comparison_contrast` is the package theorem at the same
`Y, Y'` and the real `r = ‖i‖ = 1`.  Class (b): Lean-route-only control of the abstract lemma.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickComplete

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWickComplete Finset

namespace Refutations.TerminalWickComplete.ComplexComparison

/-- `Y = (1, 0, 0, …)`. -/
noncomputable def Ya : ℕ → ℝ := fun n => if n = 0 then 1 else 0

/-- `Y' = (1, 0, 1, 0, …)`. -/
noncomputable def Yb : ℕ → ℝ := fun n => if n = 0 ∨ n = 2 then 1 else 0

theorem ya_odd : ∀ m n, Odd (m + n) → inner ℝ (Ya m) (Ya n) = 0 := by
  intro m n h
  simp only [Ya, RCLike.inner_apply, conj_trivial]
  split_ifs with h1 h2 <;> simp_all

theorem yb_odd : ∀ m n, Odd (m + n) → inner ℝ (Yb m) (Yb n) = 0 := by
  intro m n h
  simp only [Yb, RCLike.inner_apply, conj_trivial]
  split_ifs with h1 h2 <;> try simp
  exfalso
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp at h <;> exact absurd h (by decide)

theorem ya_le_yb : ∀ m n, inner ℝ (Ya m) (Ya n) ≤ inner ℝ (Yb m) (Yb n) := by
  intro m n
  simp only [Ya, Yb, RCLike.inner_apply, conj_trivial]
  split_ifs <;> simp_all

/-- The package comparison at the same `Y, Y'`, real `r = 1`. -/
theorem complex_comparison_contrast :
    ‖∑ n ∈ range 3, (1 : ℝ) ^ n • Ya n‖ ^ 2 ≤ ‖∑ n ∈ range 3, (1 : ℝ) ^ n • Yb n‖ ^ 2 :=
  norm_sq_partial_le Ya Yb ya_odd yb_odd ya_le_yb 1 (range 3)

/-- The comparison for complex `r` is false. -/
theorem complex_comparison_refuted :
    ¬ (∀ (Y Y' : ℕ → ℝ), (∀ m n, Odd (m + n) → inner ℝ (Y m) (Y n) = 0) →
      (∀ m n, Odd (m + n) → inner ℝ (Y' m) (Y' n) = 0) →
      (∀ m n, inner ℝ (Y m) (Y n) ≤ inner ℝ (Y' m) (Y' n)) →
      ∀ (r : ℂ) (s : Finset ℕ),
        ‖∑ n ∈ s, r ^ n * (Y n : ℂ)‖ ^ 2 ≤ ‖∑ n ∈ s, r ^ n * (Y' n : ℂ)‖ ^ 2) := by
  intro h
  have h1 := h Ya Yb ya_odd yb_odd ya_le_yb Complex.I (range 3)
  simp [Finset.sum_range_succ, Ya, Yb] at h1
  norm_num at h1

end Refutations.TerminalWickComplete.ComplexComparison
