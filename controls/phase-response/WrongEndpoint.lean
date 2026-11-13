module
import StratonovichHAMAudit.PhaseResponse
set_option autoImplicit false
example : 2*((3-(3/2:ℝ))/2)+(3/2) < 3 := by
  norm_num
