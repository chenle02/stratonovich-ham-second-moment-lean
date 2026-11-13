module
import StratonovichHAMAudit.PhaseResponse
set_option autoImplicit false
example : ((1:ℝ)*1/2)*1^((1:ℝ)/2-1) ≤ 0 := by
  have herr : |(0:ℝ)-1*1*1^((1:ℝ)/2-1)| ≤ 1*1^((1:ℝ)/2-2) := by norm_num
  have weakcut : (1:ℝ)/(1*1) ≤ 1 := by norm_num
  norm_num
