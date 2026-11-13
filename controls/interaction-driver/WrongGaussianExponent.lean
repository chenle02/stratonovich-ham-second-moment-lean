module
import StratonovichHAMAudit.InteractionDriver
set_option autoImplicit false
example : (1/2:ℝ)^2/(4*StratonovichHAMAudit.InteractionDriver.mixC 1 1) =
    (1/2:ℝ)^2/(4*(1+1)) := by
  norm_num [StratonovichHAMAudit.InteractionDriver.mixC]
