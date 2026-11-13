  intro p d s h i j ξ η hw
  have e : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn (Set.Icc s (s + h))
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.rowWave i)
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.colWave j) ‖ξ‖ ‖η‖ =
      StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn (Set.Icc s (s + h)) (StratonovichHAMSecondMoment.WaveTwoVariances.rowWave i)
        (StratonovichHAMSecondMoment.WaveTwoVariances.colWave j) ‖ξ‖ ‖η‖ := by
    rw [StratonovichHamSecondMomentLeanAuditBridge.MaskedContinuousWave.waveFn_eq, StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.rowWave_toP,
      StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.colWave_toP]
  have hw' : StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn (Set.Icc s (s + h)) (StratonovichHAMSecondMoment.WaveTwoVariances.rowWave i)
      (StratonovichHAMSecondMoment.WaveTwoVariances.colWave j) ‖ξ‖ ‖η‖ ∈ StratonovichHAMSecondMoment.TimeCompletion.L2fun (StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP p).T :=
    e ▸ hw
  rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.kerH_eq]
  show StratonovichHAMSecondMoment.WaveTwoVariances.kerH (StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP p) s h i j ξ η = _
  rw [_root_.StratonovichHAMSecondMoment.WaveTwoVariances.kerH_eq_smul_emb (StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP p) s h i j ξ η hw',
    StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.emb_eq p _ _ hw hw' e]
  rfl
