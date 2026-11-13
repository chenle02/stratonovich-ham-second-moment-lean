import StratonovichHAMAudit.AllAlphaMoment
example : 2*(1/2:ℝ)^2/(4+4*(1/2)) ≤ 7/100 := by
  have hmean : (43/100:ℝ)+7/100=1/2 := by norm_num
  have hweak : (43/100:ℝ)^2 ≤ 4*(7/100) := by norm_num
  norm_num
