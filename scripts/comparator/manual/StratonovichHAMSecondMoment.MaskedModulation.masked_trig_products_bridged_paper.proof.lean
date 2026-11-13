  intro E _ _ a T s h ha0 ha1 hT hh0 hh1 hs hsh A hA M D hM hD r ρ hr hρ P Q V emb hmem hnorm
  rw [StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.prodFn_eq]
  exact _root_.StratonovichHAMSecondMoment.MaskedModulation.masked_trig_products_bridged_paper
    a T s h ha0 ha1 hT hh0 hh1 hs hsh A hA M D hM hD r ρ hr hρ
    (StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.toP P)
    (StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.toP Q) V emb hmem hnorm
