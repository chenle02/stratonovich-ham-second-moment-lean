module
import StratonovichHAMAudit.GaussianTail
set_option pp.all true
#check @StratonovichHAMAudit.GaussianTail.cutoff_density_split
#print axioms StratonovichHAMAudit.GaussianTail.cutoff_density_split
example : (1 : ℝ) / 4 - 1 / 2 ≤ -(1 : ℝ) / 8 - 1 / 8 := by
  convert StratonovichHAMAudit.GaussianTail.cutoff_density_split
    1 1 (1 / 4) (3 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1 <;> norm_num
example : -(1 : ℝ) / 2 ≤ -(1 : ℝ) / 8 - 1 / 8 := by
  convert StratonovichHAMAudit.GaussianTail.cutoff_density_split
    1 1 0 (3 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1 <;> norm_num
