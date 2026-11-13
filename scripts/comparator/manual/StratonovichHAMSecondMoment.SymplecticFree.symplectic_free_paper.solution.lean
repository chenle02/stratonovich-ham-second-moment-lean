namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree
open Filter Topology Matrix
open scoped NNReal
open HomogHypothesis
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ (⊤ : ℕ∞)` (the coercion of `⊤ : ℕ∞` into `WithTop ℕ∞`)).
-- The section variables used, written as binders: {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (Rd d)} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E].
/-- Under the hypotheses of the two baseline wrappers and smooth bounded b: W_t(xi)^T Jsymp W_t(xi) = Jsymp for all t, xi; the L^2 force skewness; E:symplectic-compact-young-baseline on [0,T]; E:symplectic-compact-product-baseline. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SymplecticFree.symplectic_free_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (Rd d)} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Nontrivial E]
    (hH : HomogCovariance d alpha alpha0 Γ μ) (F : FreeWaveData d E)
    (b : Rd d → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (Cb : ℝ) (hbC : ∀ x, |b x| ≤ Cb)
    (T : ℝ) (hT : 0 < T) (θ : ℝ≥0) (hθ : 1 / 2 < θ) (hθ1 : θ < 1)
    (X : ℝ → E →L[ℝ] E) (CX : ℝ≥0) (hXhol : HolderOnWith CX θ X (Set.Icc 0 T))
    (hX0 : X 0 = 0) (hXK : ∀ r ∈ Set.Icc 0 T, IsCompactOperator (X r))
    (U : ℝ → ℝ → E →L[ℝ] E)
    (hU : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → LeftYoungSumsConverge X U s t)
    (B : ℝ) (N : ℕ) (Xs : ℕ → ℝ → E →L[ℝ] E) (CXs : ℕ → ℝ≥0)
    (hXshol : ∀ j ≤ N, HolderOnWith (CXs j) θ (Xs j) (Set.Icc 0 B))
    (hXs0 : ∀ j ≤ N, Xs j 0 = 0)
    (hXsK : ∀ j ≤ N, ∀ r ∈ Set.Icc 0 B, IsCompactOperator (Xs j r))
    (Us : ℕ → ℝ → ℝ → E →L[ℝ] E) (ℓ : ℕ → ℝ) (hℓ : ∀ j ≤ N, ℓ j ∈ Set.Icc 0 B)
    (hUs : ∀ j ≤ N, LeftYoungSumsConverge (Xs j) (Us j) 0 (ℓ j)) :
    (∀ (t : ℝ) (ξ : Rd d), (freeMatrixAt t ξ)ᵀ * Jsymp * freeMatrixAt t ξ = Jsymp) ∧
      (∀ z w : (Rd d → ℝ) × (Rd d → ℝ),
        omegaL2 MeasureTheory.volume (forceL2 b z) w
          + omegaL2 MeasureTheory.volume z (forceL2 b w) = 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        IsCompactOperator ⇑(U t s - 1 : E →L[ℝ] E) ∧
          ‖F.S (t - s)‖ ≤ ‖F.S t * U t s * F.S (-s)‖ ∧ 1 ≤ ‖F.S (t - s)‖) ∧
      (IsCompactOperator ⇑(orderedProd (fun j => F.S (ℓ j) * Us j (ℓ j) 0) N
          - F.S (∑ j ∈ Finset.range (N + 1), ℓ j)) ∧
        ‖F.S (∑ j ∈ Finset.range (N + 1), ℓ j)‖
          ≤ ‖orderedProd (fun j => F.S (ℓ j) * Us j (ℓ j) 0) N‖ ∧
        1 ≤ ‖F.S (∑ j ∈ Finset.range (N + 1), ℓ j)‖) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.SymplecticFree.symplectic_free_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree
