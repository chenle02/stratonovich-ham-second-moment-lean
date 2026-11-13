module
public import StratonovichHAMAudit.MiddleCross
/-!
Negative control for the shift in `StratonovichHAMAudit.MiddleCross.upper`.
Wrong variant (a false shortcut): the package's `resolvent b c 1` with the root shift
erased, M(0) = 1025/21483, is claimed to be at most the package's `actual b c` =
545/11616, at b = 1, c = 11/10 (0.04771... > 0.04692...). It rejects that shortcut;
it does not test the comparison J <= I of the package theorem.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
set_option autoImplicit false
example : StratonovichHAMAudit.MiddleCross.resolvent 1 (11/10) 1 ≤ StratonovichHAMAudit.MiddleCross.actual 1 (11/10) := by norm_num [StratonovichHAMAudit.MiddleCross.resolvent, StratonovichHAMAudit.MiddleCross.actual]
