/-
Refutation for the limit statement of `L:uniform-series-tail`
(`notes/notes_stratonovich_ham_second_moment.tex` lines 3707-3717 and 3738-3745
at a284420), package theorem
`StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail`.

Wrong variant: `u^i(1) → Σ X_n` from termwise convergence `Y^i_n → X_n`,
absolute convergence and nonnegative mixed moments alone, without the uniform
scaled-moment bound `‖Σ r^n Y^i_n‖² ≤ B_r` for some `r > 1`.
Counterexample in `E = ℝ`, index `i ∈ ℕ`, filter `atTop`: `Y^i_n = 1` if
`n = i` and `0` otherwise.  Each `Y^i_n → 0`, every mixed moment is `≥ 0`, every
series is a single term, but `Σ_n Y^i_n = 1` does not tend to `Σ_n 0 = 0`.
(Here `‖Σ r^n Y^i_n‖² = r^{2i}` is unbounded for every `r > 1`.)
`mass_escape_contrast`: with the bound restored (`Y^i_n = 0`), the package
theorem gives the limit.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.UniformSeriesTail

set_option autoImplicit false

open Filter Topology
open StratonovichHAMSecondMoment.UniformSeriesTail

namespace Refutations.UniformSeriesTail

/-- Auxiliary moving unit mass. -/
noncomputable def bump (i n : ℕ) : ℝ := if n = i then 1 else 0

/-- The limit statement fails without the uniform scaled-moment bound. -/
theorem mass_escape_refuted :
    ¬ (∀ (Y : ℕ → ℕ → ℝ) (X : ℕ → ℝ) (r : ℝ), 1 < r →
        (∀ i, Summable fun n => ‖r ^ n • Y i n‖) →
        (∀ i m n, 0 ≤ inner ℝ (Y i m) (Y i n)) →
        (∀ n, Tendsto (fun i => Y i n) atTop (𝓝 (X n))) →
        Tendsto (fun i => ∑' n, Y i n) atTop (𝓝 (∑' n, X n))) := by
  intro h
  have hsum : ∀ (r : ℝ) (i : ℕ), Summable fun n => ‖r ^ n • bump i n‖ := by
    intro r i
    apply summable_of_ne_finset_zero (s := {i})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [bump, hn]
  have hpos : ∀ i m n, 0 ≤ inner ℝ (bump i m) (bump i n) := by
    intro i m n
    simp only [bump]
    split_ifs <;> simp
  have hlim : ∀ n, Tendsto (fun i => bump i n) atTop (𝓝 (0 : ℝ)) := by
    intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with i hi
    simp [bump, hi.ne]
  have h1 := h bump (fun _ => 0) 2 (by norm_num) (hsum 2) hpos hlim
  have hone : (fun i => ∑' n, bump i n) = fun _ => (1 : ℝ) := by
    funext i
    simp [bump]
  rw [hone] at h1
  simp only [tsum_zero] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

/-- With the uniform bound restored (zero family), the package limit holds. -/
theorem mass_escape_contrast :
    Tendsto (fun _ : ℕ => ∑' _ : ℕ, (0 : ℝ)) atTop (𝓝 (∑' _ : ℕ, (0 : ℝ))) :=
  (uniform_series_tail atTop (fun _ _ => (0 : ℝ)) (fun _ => 0) 2 0 (by norm_num)
    (Eventually.of_forall fun _ => by simp)
    (Eventually.of_forall fun _ _ _ => by simp)
    (Eventually.of_forall fun _ => by simp)
    (fun _ => tendsto_const_nhds)).2.2.2.2

end Refutations.UniformSeriesTail
