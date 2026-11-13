module
public import StratonovichHAMAudit.TerminalCross
/-!
Negative control for `StratonovichHAMAudit.TerminalCross.rate_le`.
Wrong variant: the rate comparison with the left side `A / (2 * (A + 1))` replaced by
`A / (A + 1)` (the factor 2 dropped), in the exact shape of the package statement,
at A = 1, s = 1 / 2. The claim becomes `1 / 2 ≤ 1 / 4`. The package bound is put in
context and holds there with equality `1 / 4 ≤ 1 / 4`.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
example : (fun A s : ℝ => A / (A + 1) ≤ s * A / (A + 2 * s)) 1 (1 / 2) := by
  have h := StratonovichHAMAudit.TerminalCross.rate_le 1 (1 / 2) one_pos le_rfl
  norm_num at h ⊢
