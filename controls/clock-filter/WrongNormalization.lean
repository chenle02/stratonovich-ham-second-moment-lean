module
public import StratonovichHAMAudit.ClockFilter
/-!
Negative control for `StratonovichHAMAudit.ClockFilter.resolvent_partial_fraction`.
Wrong variant: the partial-fraction identity with the normalisation `2 * θ * ell`
replaced by `θ * ell` (the factor 2 dropped), in the exact shape of the package
statement, evaluated at θ = 1, ell = 1, r = 0. The package identity is put in
context; the goal still reduces to `3 / 8 = 3 / 4`.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
example : (fun θ ell r : ℝ =>
    (2 * θ + ell) / (2 * θ * (θ ^ 2 + r ^ 2) * ((θ + ell) ^ 2 + r ^ 2)) =
      (1 / (θ ^ 2 + r ^ 2) - 1 / ((θ + ell) ^ 2 + r ^ 2)) / (θ * ell)) 1 1 0 := by
  have h := StratonovichHAMAudit.ClockFilter.resolvent_partial_fraction 1 1 0 one_pos one_pos
  norm_num at h ⊢
