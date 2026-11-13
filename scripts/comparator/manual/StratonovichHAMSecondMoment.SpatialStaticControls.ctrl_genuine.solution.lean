namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls
open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open WeakSobolev (IsTestFunction HasWeakGradient IsRayleighTrial rayleighValue rayleighSet rayleighRate)
open VariationalDilation (CPos conv mean rawCost rate integratedRate)
open VariationalRate (score1Set S1Bdd S1pos)
-- Statement copied from the source (the printed type names the instance `WithLp.measurableSpace (2 : ENNReal) ..` explicitly, and its `2 : ENNReal` does not elaborate to the project's instance term).
-- The section variables used, written as binders: {d : ℕ} {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : Rd d → ℝ} (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x).
/-- Tempered Gamma, mu, spectral convention, 0 < a < 1, z >= 0 test, every n: each Rayleigh set of the mean of Psi_n is nonempty and bounded above, its rate is integrable on (0,1), and every cost integrand is integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpatialStaticControls.ctrl_genuine {d : ℕ} {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : Rd d → ℝ} (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (n : ℕ) :
    (∀ s, (rayleighSet (mean a Γ (ctrl a n z) s)).Nonempty ∧
      BddAbove (rayleighSet (mean a Γ (ctrl a n z) s))) ∧
    IntegrableOn (rate a Γ (ctrl a n z)) (Ioo 0 1) ∧
    (∀ σ, Integrable (fun x => ctrl a n z (σ, x) * mean a Γ (ctrl a n z) σ x)) ∧
    IntegrableOn (fun σ => ∫ x, ctrl a n z (σ, x) * mean a Γ (ctrl a n z) σ x) (Ioo 0 1) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.SpatialStaticControls.ctrl_genuine
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls
