module
public import StratonovichHAMAudit.MiddleCross
/-!
Negative control for `StratonovichHAMAudit.MiddleCross.middle_bound`.
Wrong variant: the middle bound with the prefactor 2 on the package's `upper`,
`2 * upper b c d e < actual b c`, at the root point b = 4 / 3, c = 9 / 4,
d = 29 / 12, e = 5 / 3, stated with the package definitions.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
set_option autoImplicit false
example : 2*StratonovichHAMAudit.MiddleCross.upper (4/3) (9/4) (29/12) (5/3) < StratonovichHAMAudit.MiddleCross.actual (4/3) (9/4) := by
  norm_num [StratonovichHAMAudit.MiddleCross.upper,StratonovichHAMAudit.MiddleCross.resolvent,StratonovichHAMAudit.MiddleCross.massK,StratonovichHAMAudit.MiddleCross.part1,StratonovichHAMAudit.MiddleCross.part2,StratonovichHAMAudit.MiddleCross.actual]
