module
import StratonovichHAMAudit.ProjectionResidual
set_option autoImplicit false
example : StratonovichHAMAudit.ProjectionResidual.actualMeanCoeff +
    ((3:ℝ)/2-1)*((1:ℝ)/20) ≥ ((3:ℝ)/2)*((1:ℝ)/20) := by
  norm_num [StratonovichHAMAudit.ProjectionResidual.actualMeanCoeff]
