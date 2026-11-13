  intro d s h i j ξ η
  rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.maskedKernel_eq]
  fin_cases i <;> fin_cases j <;> exact _root_.StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel_eq s h _ _ ξ η
