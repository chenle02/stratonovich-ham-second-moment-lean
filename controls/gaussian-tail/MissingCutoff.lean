module
import StratonovichHAMAudit.GaussianTail
example : (1 : ℝ) * (1 : ℝ) ^ (3 / 2 : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ -(1 : ℝ) ^ 2 / 8 - (1 : ℝ) ^ 2 / 8 := by
  norm_num
