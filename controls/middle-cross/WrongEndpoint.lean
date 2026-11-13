module
public import StratonovichHAMAudit.MiddleCross
/-!
Negative control for `StratonovichHAMAudit.MiddleCross.middle_bound`.
Wrong variant: the strict middle bound `upper b c (√(b²+c²-1)) (√(b²+1)) < actual b c`
at the excluded endpoint c = 1 (the package assumes `1 < c`), stated with the package
definitions `upper`, `resolvent`, `massK`, `part1`, `part2`, `actual`, at b = 4 / 3,
where the square roots are 4 / 3 and 5 / 3.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
set_option autoImplicit false
example : StratonovichHAMAudit.MiddleCross.upper (4/3) 1 (Real.sqrt (((4:ℝ)/3)^2+1^2-1)) (Real.sqrt (((4:ℝ)/3)^2+1)) < StratonovichHAMAudit.MiddleCross.actual (4/3) 1 := by
  have hd : ((4:ℝ)/3)^2+1^2-1 = ((4:ℝ)/3)^2 := by norm_num
  have he : ((4:ℝ)/3)^2+1 = ((5:ℝ)/3)^2 := by norm_num
  rw [hd,he]
  norm_num [Real.sqrt_sq_eq_abs,StratonovichHAMAudit.MiddleCross.upper,StratonovichHAMAudit.MiddleCross.resolvent,StratonovichHAMAudit.MiddleCross.massK,StratonovichHAMAudit.MiddleCross.part1,StratonovichHAMAudit.MiddleCross.part2,StratonovichHAMAudit.MiddleCross.actual]
