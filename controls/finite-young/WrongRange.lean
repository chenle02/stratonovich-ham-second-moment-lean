import StratonovichHAMAudit.FiniteYoung
example : |(2:ℝ)|^3 * |(1:ℝ)|^(2-3:ℕ) ≤
    (3:ℝ)/(2:ℝ)*|(2:ℝ)|^2 + ((2-3:ℕ):ℝ)/(2:ℝ)*|(1:ℝ)|^2 := by
  norm_num
