module
import StratonovichHAMAudit.LocalFlow
example : -(1:ℝ)/2 < StratonovichHAMAudit.LocalFlow.sourceSigma 1 := by
  norm_num [StratonovichHAMAudit.LocalFlow.sourceSigma]
