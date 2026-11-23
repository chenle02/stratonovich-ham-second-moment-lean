/-
Refutation for the parity hypotheses of the partial-sum comparison of `L:terminal-wick` (main
TeX lines 4329 and 4331-4333, proof 4404-4406 at edf7085f), package theorem
`StratonovichHAMSecondMoment.TerminalWickComplete.norm_sq_partial_le`.

Wrong variant: the partial-sum comparison from the entrywise comparison of the Gram entries
alone, without the vanishing of the odd mixed moments (TeX line 4329) for the larger family.
For negative `r` the odd cross terms enter with the negative coefficient `r^{m+n}`.
Counterexample in `ℝ`: `Y = (1, 0)`, `Y' = (1, 1)` (entrywise `Y_m Y_n ≤ Y'_m Y'_n`, but
`Y'_0 Y'_1 = 1 ≠ 0`), `r = -1`, `s = {0,1}`: `|1|² = 1` but `|1 - 1|² = 0`.
`no_parity_contrast` is the package theorem at the same `Y` and the parity-respecting
`Y'' = (1, 0)`.  Class (b): Lean-route-only control (for the constructed chain integrals the
parity hypothesis is `mixed_moment_odd`, always available).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickComplete

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWickComplete Finset

namespace Refutations.TerminalWickComplete.NoParity

/-- `Y = (1, 0, 0, …)`. -/
noncomputable def Ya : ℕ → ℝ := fun n => if n = 0 then 1 else 0

/-- `Y' = (1, 1, 0, …)`. -/
noncomputable def Yb : ℕ → ℝ := fun n => if n = 0 ∨ n = 1 then 1 else 0

theorem ya_odd : ∀ m n, Odd (m + n) → inner ℝ (Ya m) (Ya n) = 0 := by
  intro m n h
  simp only [Ya, RCLike.inner_apply, conj_trivial]
  split_ifs with h1 h2 <;> simp_all

theorem ya_le_yb : ∀ m n, inner ℝ (Ya m) (Ya n) ≤ inner ℝ (Yb m) (Yb n) := by
  intro m n
  simp only [Ya, Yb, RCLike.inner_apply, conj_trivial]
  split_ifs <;> simp_all

/-- The package comparison at the same `Y` and `Y'' = Y` (which respects the parity). -/
theorem no_parity_contrast :
    ‖∑ n ∈ range 2, (-1 : ℝ) ^ n • Ya n‖ ^ 2 ≤ ‖∑ n ∈ range 2, (-1 : ℝ) ^ n • Ya n‖ ^ 2 :=
  norm_sq_partial_le Ya Ya ya_odd ya_odd (fun _ _ => le_rfl) (-1) (range 2)

/-- Without the parity hypothesis on the larger family, the comparison is false. -/
theorem no_parity_refuted :
    ¬ (∀ (Y Y' : ℕ → ℝ), (∀ m n, Odd (m + n) → inner ℝ (Y m) (Y n) = 0) →
      (∀ m n, inner ℝ (Y m) (Y n) ≤ inner ℝ (Y' m) (Y' n)) →
      ∀ (r : ℝ) (s : Finset ℕ),
        ‖∑ n ∈ s, r ^ n • Y n‖ ^ 2 ≤ ‖∑ n ∈ s, r ^ n • Y' n‖ ^ 2) := by
  intro h
  have h1 := h Ya Yb ya_odd ya_le_yb (-1) (range 2)
  simp [Finset.sum_range_succ, Ya, Yb] at h1
  norm_num at h1

end Refutations.TerminalWickComplete.NoParity
