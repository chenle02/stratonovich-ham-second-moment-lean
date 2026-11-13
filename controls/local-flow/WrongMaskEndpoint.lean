module
import StratonovichHAMAudit.LocalFlow
example : StratonovichHAMAudit.LocalFlow.noiseOrder 0 < (1:ℝ)/2 := by
  norm_num [StratonovichHAMAudit.LocalFlow.noiseOrder]
