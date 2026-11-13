module
import StratonovichHAMAudit.PhaseResponse
set_option autoImplicit false
example : 2*(1:ℝ)+1+1/2 < 3 := by
  norm_num
