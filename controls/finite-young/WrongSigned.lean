import StratonovichHAMAudit.FiniteYoung
example : (-2:ℝ)^2 * (1:ℝ)^(3-2:ℕ) ≤
    (2:ℝ)/(3:ℝ)*(-2:ℝ)^3 + ((3-2:ℕ):ℝ)/(3:ℝ)*(1:ℝ)^3 := by
  norm_num
