namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask
open MeasureTheory Set Metric Filter Topology
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open WeakSobolev
open VariationalDilation (CPos SetScaling mean rawCost rate integratedRate)
open VariationalFloor (fl gl)
open VariationalRate (psiBar)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- Under HomogCovariance, Gamma != 0, Psi in CPos d and RawBlockOriginalLower alpha0 Gamma Psi (rawCost alpha0 Gamma Psi) L: the rate part and (2 I_Psi - v_Psi/2 : EReal) <= liminf over T -> infinity of L T. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RemoveMask.variational_remove_mask_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) {L : ℝ → ℝ}
    (hRB : RawBlockOriginalLower alpha0 Γ Ψ (rawCost alpha0 Γ Ψ) L) :
    (∀ R, 0 < R →
      ContDiff ℝ ∞ (mask (d := d) R) ∧ (∀ x : Rd d, mask R (-x) = mask R x) ∧
      (∀ x y : Rd d, ‖x‖ = ‖y‖ → mask R x = mask R y) ∧
      (∀ x : Rd d, 0 ≤ mask R x ∧ mask R x ≤ 1) ∧ (∀ x : Rd d, ‖x‖ ≤ R → mask R x = 1) ∧
      tsupport (mask (d := d) R) ⊆ closedBall 0 (2 * R)) ∧
    (∀ R R', 0 < R → R ≤ R' → ∀ x : Rd d, mask R x ≤ mask R' x) ∧
    (∀ x : Rd d, Tendsto (fun R => mask R x) atTop (𝓝 1)) ∧
    (∃ ε M C R₀ : ℝ, 0 < ε ∧ ε ≤ M ∧ 0 ≤ C ∧ 0 < R₀ ∧
      (∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1,
        (rayleighSet (maskedMean alpha0 Γ Ψ R s)).Nonempty ∧
        BddAbove (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        ε ≤ sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ≤ M ∧
        maskedRate alpha0 Γ Ψ R s ^ 2 = sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        Real.sqrt ε ≤ maskedRate alpha0 Γ Ψ R s ∧ maskedRate alpha0 Γ Ψ R s ≤ Real.sqrt M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ R R', 0 < R → R ≤ R' →
        maskedRate alpha0 Γ Ψ R s ≤ maskedRate alpha0 Γ Ψ R' s ∧
        maskedRate alpha0 Γ Ψ R' s ≤ rate alpha0 Γ Ψ s) ∧
      (∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |maskedRate alpha0 Γ Ψ R s - maskedRate alpha0 Γ Ψ R t| ≤
          C / (2 * Real.sqrt ε) * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        sSup ((fun R => sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s))) '' Ici R₀) =
          sSup (rayleighSet (mean alpha0 Γ Ψ s))) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        Tendsto (fun R => maskedRate alpha0 Γ Ψ R s) atTop (𝓝 (rate alpha0 Γ Ψ s))) ∧
      TendstoUniformlyOn (fun R s => maskedRate alpha0 Γ Ψ R s) (rate alpha0 Γ Ψ) atTop (Icc 0 1) ∧
      (∀ R, R₀ ≤ R → IntegrableOn (maskedRate alpha0 Γ Ψ R) (Ioo 0 1)) ∧
      (∀ R R', R₀ ≤ R → R ≤ R' →
        maskedIntegratedRate alpha0 Γ Ψ R ≤ maskedIntegratedRate alpha0 Γ Ψ R' ∧
        maskedIntegratedRate alpha0 Γ Ψ R' ≤ integratedRate alpha0 Γ Ψ) ∧
      Tendsto (maskedIntegratedRate alpha0 Γ Ψ) atTop (𝓝 (integratedRate alpha0 Γ Ψ))) ∧
    ((2 * integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 : ℝ) : EReal) ≤
      liminf (fun T => (L T : EReal)) atTop := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask
