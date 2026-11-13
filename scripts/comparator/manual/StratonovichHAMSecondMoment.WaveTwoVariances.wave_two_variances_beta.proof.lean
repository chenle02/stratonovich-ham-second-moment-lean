  intro α a γ β ha hαa hγ0 hγ hαγ hβa hβα
  obtain ⟨K, hK, H⟩ := _root_.StratonovichHAMSecondMoment.WaveTwoVariances.wave_two_variances_beta ha hαa hγ0 hγ hαγ hβa hβα
  refine ⟨K, hK, fun p hp d ν C hC hball s h h0 h1 hs hsT => ?_⟩
  rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.inputBound_eq, StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.outputBound_eq]
  exact H (StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP p) hp d ν C hC hball s h h0 h1 hs hsT
