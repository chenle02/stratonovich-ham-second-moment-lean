namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
open Real Set MeasureTheory Filter Topology
open StratonovichHAMSecondMoment.StaticPhaseCauchy
-- Statement copied from the source (the printed type elaborates the semiring structure of `ℂ` as `Complex.instSemiring`, the declaration through `RCLike`).
-- The section variables and scoped opens of the source, as there:
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Under the hypotheses of interval_complex_range_paper, supplied Crouzeix-Palencia bounds on numRange (A0 - V) and Q' - 1 = (1/pi) int J, ||J t|| <= (D/(1-deltaA a)) t^(-1/2)(Lam^2+t)^((a-3)/2): adjoint sandwich, range, operator and Neumann bounds, block bound 100 e^(2 Lam h). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ComplexPhaseScalar.interval_complex_paper (A0 V : H →L[ℂ] H) (hA0 : A0.IsPositive) {a D : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hsand : ∀ ρ > 0, ‖invSqrtShift A0 ρ * V * invSqrtShift A0 ρ‖ ≤ D * ρ ^ (a - 2))
    {Λ : ℝ} (hΛ : 0 < Λ) (hD : D ≤ deltaA a * Λ ^ (2 - a)) {h : ℝ} (hh : 0 ≤ h)
    (Cop Fop Hop : H →L[ℂ] H)
    (hCPC : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - V), ‖phaseC h w‖ ≤ M) → ‖Cop‖ ≤ (1 + √2) * M)
    (hCPF : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - V), ‖phaseF h Λ w‖ ≤ M) → ‖Fop‖ ≤ (1 + √2) * M)
    (hCPH : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - V), ‖phaseH h Λ w‖ ≤ M) → ‖Hop‖ ≤ (1 + √2) * M)
    (Q' : H →L[ℂ] H) (J : ℝ → H →L[ℂ] H) (hJm : AEStronglyMeasurable J (volume.restrict (Ioi 0)))
    (hJ : ∀ t ∈ Ioi (0 : ℝ),
      ‖J t‖ ≤ D / (1 - deltaA a) * (t ^ (-(1 / 2 : ℝ)) * (Λ ^ 2 + t) ^ ((a - 3) / 2)))
    (hQ' : Q' - 1 = (1 / π) • ∫ t in Ioi (0 : ℝ), J t) :
    (∀ ρ > 0, ‖invSqrtShift A0 ρ * ContinuousLinearMap.adjoint V * invSqrtShift A0 ρ‖ ≤
        D * ρ ^ (a - 2)) ∧
      (∀ w ∈ numRange (A0 - V), PhaseRangeBounds a (deltaA a) Λ h w) ∧
      ‖Cop‖ ≤ 3 * Real.exp (Λ * h) ∧ ‖Fop‖ ≤ 6 * (1 + Λ * h) * Real.exp (Λ * h) ∧
      ‖Hop‖ ≤ 6 * Real.exp (Λ * h) ∧ ‖Q' - 1‖ ≤ 1 / 6 ∧ IsUnit Q' ∧
      ‖ContinuousLinearMap.adjoint Q'‖ ≤ 7 / 6 ∧
      ‖ContinuousLinearMap.adjoint (Ring.inverse Q')‖ ≤ 6 / 5 ∧
      ∀ u v : H,
        √(‖Cop u + (Fop ∘L ContinuousLinearMap.adjoint Q') v‖ ^ 2 +
            ‖(-(ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Hop)) u +
              (ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Cop ∘L
                ContinuousLinearMap.adjoint Q') v‖ ^ 2) ≤
          100 * Real.exp (2 * (Λ * h)) * √(‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ComplexPhaseScalar.interval_complex_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
