import StratonovichHAMAudit.DimensionalMatrix
-- For cp=cq=H=1 and sp=sq=0, the lower-left entry is 1, not 0.
example : ((StratonovichHAMAudit.DimensionalMatrix.backward 1 0 1 *
  StratonovichHAMAudit.DimensionalMatrix.coupling 1 *
  StratonovichHAMAudit.DimensionalMatrix.forward 1 0 1) 1 0) = 0 := by
  norm_num [StratonovichHAMAudit.DimensionalMatrix.backward,
    StratonovichHAMAudit.DimensionalMatrix.coupling,
    StratonovichHAMAudit.DimensionalMatrix.forward,Matrix.mul_apply,Fin.sum_univ_two]
