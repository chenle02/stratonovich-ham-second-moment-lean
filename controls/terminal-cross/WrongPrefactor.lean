module
public import StratonovichHAMAudit.TerminalCross
/-!
Negative control for `StratonovichHAMAudit.TerminalCross.terminal_bound`.
Wrong variant: the terminal bound with the left prefactor `16 * c ^ 3` replaced by
`4 * c ^ 3`, in the exact shape of the package statement with the package's `numP`
and `numN`, at b = 1, c = 7, where the square root is `7 / 5`. The claim becomes
`1140 / 307328 < 816 / 307328` (the correct left side is `285 / 307328`).
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
example : (fun b c : ℝ =>
    StratonovichHAMAudit.TerminalCross.numP c /
        (4 * c ^ 3 * (c + 1) * Real.sqrt (b ^ 2 + (c ^ 2 - 1) / (c ^ 2 + 1))) <
      StratonovichHAMAudit.TerminalCross.numN b c / (32 * c ^ 3 * (b + c - 1) * (b + 1))) 1 7 := by
  have hr : (1 : ℝ) ^ 2 + ((7 : ℝ) ^ 2 - 1) / ((7 : ℝ) ^ 2 + 1) = ((7 : ℝ) / 5) ^ 2 := by norm_num
  show _ / (_ * Real.sqrt ((1 : ℝ) ^ 2 + ((7 : ℝ) ^ 2 - 1) / ((7 : ℝ) ^ 2 + 1))) < _
  rw [hr, Real.sqrt_sq (by norm_num)]
  norm_num [StratonovichHAMAudit.TerminalCross.numP, StratonovichHAMAudit.TerminalCross.numN]
