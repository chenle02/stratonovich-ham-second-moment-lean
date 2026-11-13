module
import StratonovichHAMAudit.DirectEvent
set_option autoImplicit false
example : -(1/2:ℝ)/2 + (1-StratonovichHAMAudit.DirectEvent.kappa 1 (1/2))*(2-1/2) =
    -StratonovichHAMAudit.DirectEvent.kappa 1 (1/2) := by
  norm_num [StratonovichHAMAudit.DirectEvent.kappa]
