import StratonovichHAMAudit.DampedLower
-- The weaker lower number 3 does not clear the required cubic threshold.
example : (9:ℝ)*2^25/5^10 < 3^3 := by
  norm_num
