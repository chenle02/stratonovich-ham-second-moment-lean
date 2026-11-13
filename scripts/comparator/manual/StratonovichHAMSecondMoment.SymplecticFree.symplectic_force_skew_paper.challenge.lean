namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree
open Filter Topology Matrix
open scoped NNReal
open HomogHypothesis
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ (⊤ : ℕ∞)` (the coercion of `⊤ : ℕ∞` into `WithTop ℕ∞`)).
-- The section variables used, written as binders: {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (Rd d)}.
/-- Under H:homog (unused), for smooth b : R^d -> R with |b x| <= C: x -> f x * (b x * u x) is Lebesgue integrable for u, f in L^2, and omegaL2 (forceL2 b z) w + omegaL2 z (forceL2 b w) = 0 for all pairs z, w. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SymplecticFree.symplectic_force_skew_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (Rd d)} (_hH : HomogCovariance d alpha alpha0 Γ μ)
    (b : Rd d → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (C : ℝ) (hbC : ∀ x, |b x| ≤ C) :
    (∀ u f : Rd d → ℝ, MeasureTheory.MemLp u 2 MeasureTheory.volume →
        MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.Integrable (fun x => f x * (b x * u x)) MeasureTheory.volume) ∧
      ∀ z w : (Rd d → ℝ) × (Rd d → ℝ),
        omegaL2 MeasureTheory.volume (forceL2 b z) w
          + omegaL2 MeasureTheory.volume z (forceL2 b w) = 0 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree
