module
public import StratonovichHAMAudit.TerminalCross
/-!
Negative control for `StratonovichHAMAudit.TerminalCross.polynomial_pos`.
Wrong variant: the package's terminal polynomial `polynomial b c` is nonpositive
(the package proves it positive for `1 ≤ b`, `1 < c`), at b = 1, c = 2, where the
package definitions `polynomial`, `numP`, `numN` evaluate to a positive number.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
example : StratonovichHAMAudit.TerminalCross.polynomial 1 2 ≤ 0 := by
  norm_num [StratonovichHAMAudit.TerminalCross.polynomial, StratonovichHAMAudit.TerminalCross.numP, StratonovichHAMAudit.TerminalCross.numN]
