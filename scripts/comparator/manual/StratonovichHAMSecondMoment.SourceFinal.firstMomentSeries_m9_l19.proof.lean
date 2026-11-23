  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (intro d alpha α₀ Γ μ hH t ht x
   have h := _root_.StratonovichHAMSecondMoment.SourceFinal.first_moment_series_l19.{0} d
     (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) _
     (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.m9 (fun {alpha α₀ Γ μ} => StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal.source_field_l19 d) hH).W
     (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP
       (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.m9 (fun {alpha α₀ Γ μ} => StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal.source_field_l19 d) hH).field)
     t ht x
   simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq]
   exact h)
