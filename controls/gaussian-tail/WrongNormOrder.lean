module
import StratonovichHAMAudit.GaussianTail
example : (0 : ℝ) * (1 : ℝ) ^ (3 / 2 : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ -(3 : ℝ) ^ 2 / 8 - (1 : ℝ) ^ 2 / 8 := by
  norm_num
