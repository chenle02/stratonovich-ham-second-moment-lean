module
public import StratonovichHAMAudit.MiddleCross
/-!
Negative control for the parametrisation used in
`StratonovichHAMAudit.MiddleCross.root_numerator_pos` (t = (d + c) / (b + 1)).
Wrong variant: the inverse parameter built with `b - 1` in place of `b + 1`,
t = (d + c) / (b - 1), at b = 4 / 3, c = 9 / 4, d = 29 / 12 (z = 3, so
`paramB 3 = 4 / 3`), claiming the package's `paramC 3 t` recovers c = 9 / 4.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
set_option autoImplicit false
example : StratonovichHAMAudit.MiddleCross.paramC 3 (((29:ℝ)/12+9/4)/(4/3-1)) = 9/4 := by norm_num [StratonovichHAMAudit.MiddleCross.paramC,StratonovichHAMAudit.MiddleCross.paramB]
