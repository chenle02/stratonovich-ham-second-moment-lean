module
public import StratonovichHAMAudit.MiddleCross
/-!
Negative control for `StratonovichHAMAudit.MiddleCross.root_numerator_pos`.
Wrong variant: the package's `numerator b c d e` is nonpositive at the root point
b = 4 / 3, c = 9 / 4, d = √(b²+c²-1) = 29 / 12, e = √(b²+1) = 5 / 3 (the package
proves it positive there).
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
set_option autoImplicit false
example : StratonovichHAMAudit.MiddleCross.numerator (4/3) (9/4) (29/12) (5/3) ≤ 0 := by norm_num [StratonovichHAMAudit.MiddleCross.numerator]
