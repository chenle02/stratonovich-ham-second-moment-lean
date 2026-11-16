namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszPositiveDefinite
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Filter
open scoped ENNReal NNReal Topology
open HomogHypothesis (Rd IsTempered IsPosDefDistr)
open EndpointLemmas
open EndpointCorollaries
/-- For a linear isometry iota : R^m -> R^d, s-finite nu carried by s >= 0, measurable finite f = int gauss s dnu a.e., f dx tempered: the image iota_*(f dx) is positive definite. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszPositiveDefinite.posdef_of_mixture {m d : ℕ} (ι : Rd m →ₗᵢ[ℝ] Rd d) (ν : Measure (Fin m → ℝ))
    [SFinite ν] (hν : ∀ᵐ s ∂ν, ∀ j, 0 ≤ s j) {f : Rd m → ℝ≥0∞} (hfm : Measurable f)
    (hfin : ∀ x, f x < ∞) (hf : ∀ᵐ x, f x = ∫⁻ s, ENNReal.ofReal (gauss s x) ∂ν)
    (ht : IsTempered ((volume : Measure (Rd m)).withDensity f)) :
    IsPosDefDistr (((volume : Measure (Rd m)).withDensity f).map ι) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.RieszPositiveDefinite.posdef_of_mixture
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszPositiveDefinite
