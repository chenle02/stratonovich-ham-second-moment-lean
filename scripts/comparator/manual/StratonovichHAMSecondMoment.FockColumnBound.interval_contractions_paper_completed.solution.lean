namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (bridge_auto needs more heartbeats than the default for this statement).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
open HomogHypothesis (IsTempered IsEven IsSpectralMeasure HomogCovariance)
open SpectralHomog (SpectralHomogeneous)
open SpectralMassIdentity (ralpha)
open HermiteFock (Supp degLE fieldOp iota)
set_option maxHeartbeats 4000000 in
/-- Under HomogCovariance d alpha alpha0 Gamma mu, R = R_alpha, eps, rho > 0, orthonormal real modes psi_i in L^2(nuEps mu eps), S = sqrtResolvent rho, M = modes, P = bandProj b: conclusions (a)-(d) of FockForm.interval_contractions for these operators. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.interval_contractions_paper_completed {d : ℕ} {alpha alpha0 R ε ρ b : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (hρ : 0 < ρ) {m : ℕ} (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ)) :
    let S := sqrtResolvent (d := d) ρ hρ
    let M := modes (nuEps_finite hH.μ_tempered hε) ψ hψ
    let P := bandProj (d := d) b
    FockForm.FockColumn (fun i => S ∘L (P ∘L M i ∘L P)) (R * ρ ^ (alpha - 2)) ∧
      (∀ u w : Lp ℂ 2 (volume : Measure (Rd d)),
        Integrable (fun x => ‖∑ i, ((x i : ℝ) : ℂ) • (S ∘L (P ∘L M i ∘L P)) u‖ ^ 2)
          (GaussianIBP.stdPi m) ∧
        ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • (S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ∂GaussianIBP.stdPi m =
          ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ∧
        ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ≤ R * ρ ^ (alpha - 2) * (‖u‖ ^ 2 + ‖S w‖ ^ 2)) ∧
      (∀ i, IsSelfAdjoint (S ∘L (P ∘L M i ∘L P) ∘L S)) ∧
      FockForm.FockColumn (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) (R * ρ ^ (alpha - 4)) ∧
      ∀ (N : ℕ) (v : (Fin m → ℕ) → Lp ℂ 2 (volume : Measure (Rd d))), Supp N v →
        ∑ k ∈ degLE m N, ‖fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v k‖ ^ 2 ≤
          (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
            ∑ k ∈ degLE m N, ‖v k‖ ^ 2 ∧
        Integrable (fun x => ‖iota N (fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v) x‖ ^ 2)
          (GaussianIBP.stdPi m) ∧
        ∫ x, ‖iota N (fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v) x‖ ^ 2
            ∂GaussianIBP.stdPi m ≤
          (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
            ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m := by
  bridge_revert_all
  bridge_rw
  intro d alpha alpha0 R ε ρ b Γ μ hH hRdef hε hρ m ψ hψ hreal
  first
    | exact _root_.StratonovichHAMSecondMoment.FockColumnBound.interval_contractions_paper_completed (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) hRdef hε hρ ψ hψ hreal
    | exact _root_.StratonovichHAMSecondMoment.FockColumnBound.interval_contractions_paper_completed hH hRdef hε hρ ψ hψ hreal
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
