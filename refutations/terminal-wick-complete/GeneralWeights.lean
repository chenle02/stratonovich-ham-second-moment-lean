/-
Refutation for the power structure of the partial-sum comparison of `L:terminal-wick` (main TeX
lines 4331-4333, proof 4404-4406 at edf7085f), package theorem
`StratonovichHAMSecondMoment.TerminalWickComplete.norm_sq_partial_le`.

Wrong variant: the comparison for arbitrary real weights, `‖Σ_{n∈s} a_n Y_n‖² ≤ ‖Σ_{n∈s} a_n
Y'_n‖²`, instead of the powers `a_n = r^n` (whose products `r^m r^n = r^{m+n}` are nonnegative
whenever `m + n` is even).  Counterexample in `ℝ`: `Y = (1, 0, 0)`, `Y' = (1, 0, 1)` (all the
hypotheses of the package theorem hold), `a = (1, 0, -1)`: `|1|² = 1` but `|1 - 1|² = 0`.
`general_weights_contrast` is the package theorem at the same `Y, Y'` with `r = -1`, whose
weights `(1, -1, 1)` agree with `a` up to the sign at the even index `2`.  Class (b):
Lean-route-only control of the abstract lemma.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickComplete

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWickComplete Finset

namespace Refutations.TerminalWickComplete.GeneralWeights

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

/-- The package comparison at the same `Y, Y'`, `r = -1`. -/
theorem general_weights_contrast :
    ‖∑ n ∈ range 3, (-1 : ℝ) ^ n • Ya n‖ ^ 2 ≤ ‖∑ n ∈ range 3, (-1 : ℝ) ^ n • Yb n‖ ^ 2 :=
  norm_sq_partial_le Ya Yb ya_odd yb_odd ya_le_yb (-1) (range 3)

/-- The comparison for arbitrary real weights is false. -/
theorem general_weights_refuted :
    ¬ (∀ (Y Y' : ℕ → ℝ), (∀ m n, Odd (m + n) → inner ℝ (Y m) (Y n) = 0) →
      (∀ m n, Odd (m + n) → inner ℝ (Y' m) (Y' n) = 0) →
      (∀ m n, inner ℝ (Y m) (Y n) ≤ inner ℝ (Y' m) (Y' n)) →
      ∀ (a : ℕ → ℝ) (s : Finset ℕ),
        ‖∑ n ∈ s, a n • Y n‖ ^ 2 ≤ ‖∑ n ∈ s, a n • Y' n‖ ^ 2) := by
  intro h
  have h1 := h Ya Yb ya_odd yb_odd ya_le_yb (fun n => if n = 2 then -1 else 1) (range 3)
  simp [Finset.sum_range_succ, Ya, Yb] at h1
  norm_num at h1

end Refutations.TerminalWickComplete.GeneralWeights
