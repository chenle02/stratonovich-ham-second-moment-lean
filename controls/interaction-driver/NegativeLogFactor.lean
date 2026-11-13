module
import StratonovichHAMAudit.InteractionDriver
set_option autoImplicit false
example : Real.sqrt ((1:ℝ)*1^(2-(1/2:ℝ))*(-2)^2) =
    Real.sqrt (1:ℝ)*1^(1-(1/2:ℝ)/2)*(-2) := by
  norm_num
