module
public import StratonovichHAMAudit.TerminalCross
/-!
Negative control for `StratonovichHAMAudit.TerminalCross.terminal_bound`.
Wrong variant: the strict terminal bound at the excluded endpoint c = 1 (the package
assumes `1 < c`), in the exact shape of the package statement with the package's
`numP` and `numN`, at b = 1, c = 1. Both sides equal `3 / 32`, so the strict claim
is `3 / 32 < 3 / 32`.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
example : (fun b c : ℝ =>
    StratonovichHAMAudit.TerminalCross.numP c /
        (16 * c ^ 3 * (c + 1) * Real.sqrt (b ^ 2 + (c ^ 2 - 1) / (c ^ 2 + 1))) <
      StratonovichHAMAudit.TerminalCross.numN b c / (32 * c ^ 3 * (b + c - 1) * (b + 1))) 1 1 := by
  norm_num [StratonovichHAMAudit.TerminalCross.numP, StratonovichHAMAudit.TerminalCross.numN]
