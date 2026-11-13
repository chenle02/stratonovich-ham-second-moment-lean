module
import StratonovichHAMAudit.DirectEvent
set_option autoImplicit false
example : (StratonovichHAMAudit.DirectEvent.gauge (-(1:ℝ)/100) *
    StratonovichHAMAudit.DirectEvent.drift *
    StratonovichHAMAudit.DirectEvent.gauge ((1:ℝ)/100)) (1:Fin 2) 0 = 1 := by
  norm_num [StratonovichHAMAudit.DirectEvent.gauge,
    StratonovichHAMAudit.DirectEvent.drift, Matrix.mul_apply, Fin.sum_univ_two]
