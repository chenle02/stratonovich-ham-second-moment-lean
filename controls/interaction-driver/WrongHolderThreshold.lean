module
import StratonovichHAMAudit.InteractionDriver
set_option autoImplicit false
example : 0 < (3/4:ℝ)-StratonovichHAMAudit.InteractionDriver.midpoint (3/4) (5/8)-1/12 := by
  have weakcut : (1:ℝ)/(3/4-5/8) < 12 := by norm_num
  norm_num [StratonovichHAMAudit.InteractionDriver.midpoint]
