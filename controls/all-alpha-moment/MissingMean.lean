import StratonovichHAMAudit.AllAlphaMoment
example : 2*(1/2:ℝ)^2/(4+4*(1/2)) ≤ 0 := by
  have hweak : (0:ℝ)+0 ≤ 1/2 := by norm_num
  have hcs : (0:ℝ)^2 ≤ 4*0/2 := by norm_num
  norm_num
