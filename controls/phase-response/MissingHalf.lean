module
import StratonovichHAMAudit.PhaseResponse
set_option autoImplicit false
example : Real.cos (0:ℝ)*Real.cos 0 = Real.cos (0-0)+Real.cos (0+0) := by
  norm_num
