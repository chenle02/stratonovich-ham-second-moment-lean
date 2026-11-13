module
public import StratonovichHAMAudit.ClockFilter
/-!
Negative control for `StratonovichHAMAudit.ClockFilter.clock_filter_bounds`.
Wrong variant: the clock filter `2 * θ / (2 * θ + ell)` is at least 1 (the package
proves it is strictly below 1), evaluated at θ = 1, ell = 1, where it equals 2 / 3.
The package bound is put in context; the goal still reduces to `1 ≤ 2 / 3`.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
example : (fun θ ell : ℝ => 1 ≤ 2 * θ / (2 * θ + ell)) 1 1 := by
  have h := StratonovichHAMAudit.ClockFilter.clock_filter_bounds 1 1 one_pos one_pos
  norm_num at h ⊢
