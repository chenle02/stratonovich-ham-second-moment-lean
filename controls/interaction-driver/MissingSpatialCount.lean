module
import StratonovichHAMAudit.InteractionDriver
set_option autoImplicit false
example : 0 < (1-(1/2:ℝ))/2-2/6 := by
  have weakcut : (2:ℝ)/(1-1/2) < 6 := by norm_num
  norm_num
