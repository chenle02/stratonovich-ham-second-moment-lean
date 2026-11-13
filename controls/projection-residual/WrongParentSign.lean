module
import StratonovichHAMAudit.ProjectionResidual
set_option autoImplicit false
example : StratonovichHAMAudit.ProjectionResidual.actualMeanCoeff ≥ (1:ℝ)/48 := by
  norm_num [StratonovichHAMAudit.ProjectionResidual.actualMeanCoeff]
