namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)
open TimeSchur (kern kern_nonneg measurable_kern)
open VariationalDilation (CPos conv mean rawCost)
-- Statement copied from the source (the printed type unfolds `Rd d` to `EuclideanSpace ℝ (Fin d)` (a `WithLp` type) at one occurrence where the declaration keeps `Rd d`).
-- The section variables used, written as binders: {d : ℕ}.
/-- If HomogCovariance d alpha alpha0 Gamma mu, Gamma != 0, a = alpha0, Psi in CPos d, g CC on R x R^d: A(g) = stForm a Gamma g^2 g^2 has integrable integrand, A(g) >= 0; int_(0,1) int h_t g_t^2 is integrable, equals stForm a Gamma Psi g^2, and is <= sqrt(rawCost a Gamma Psi A(g)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpaceTimePositivity.occupation_raw_square_cc_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) {a : ℝ} (ha : a = alpha0)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {g : ℝ × Rd d → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2) *
        stPair Γ (fun p => g p ^ 2) (fun p => g p ^ 2) p) (timeMeasure.prod timeMeasure) ∧
      0 ≤ stForm a Γ (fun p => g p ^ 2) (fun p => g p ^ 2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean a Γ Ψ t x * g (t, x) ^ 2)) ∧
      IntegrableOn (fun t => ∫ x, mean a Γ Ψ t x * g (t, x) ^ 2) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * g (t, x) ^ 2 =
        stForm a Γ Ψ (fun p => g p ^ 2) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * g (t, x) ^ 2 ≤
        Real.sqrt (rawCost a Γ Ψ * stForm a Γ (fun p => g p ^ 2) (fun p => g p ^ 2)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity
