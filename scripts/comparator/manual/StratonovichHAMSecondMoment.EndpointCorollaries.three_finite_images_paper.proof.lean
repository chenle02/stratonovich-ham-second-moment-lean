  bridge_rw
  intro hPD hIso hPl Mdl α₀ α hT h0 h1 h2 h3 N X hX T w hw hwpos
  have h := _root_.StratonovichHAMSecondMoment.EndpointCorollaries.three_finite_images_paper hPD hIso hPl (StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmToP Mdl) (StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttToP hT)
    h0 h1 h2 h3 (fun i => StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.compToP (X i)) (fun i => StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.valid_toP (hX i)) T hw hwpos
  simp only [← StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.meas_eq, ← StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.low_eq, ← StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.st_eq] at h
  exact h
