namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
open Real Set MeasureTheory Filter Topology
open StratonovichHAMSecondMoment.StaticPhaseCauchy
-- Statement copied from the source (the printed type elaborates the semiring structure of `ℂ` as `Complex.instSemiring`, the declaration through `RCLike`).
-- The section variables and scoped opens of the source, as there:
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Under the hypotheses of complex_phase_range_paper, supplied Crouzeix-Palencia bounds on numRange (A0 - z B) and Q' - 1 = (1/pi) int J, ||J t|| <= (||z|| d/(1-deltaA a)) t^(-1/2)(lam^2+t)^((a-3)/2): range bounds, operator and Neumann bounds, block bound 100 e^(2 lam h). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ComplexPhaseScalar.complex_phase_paper (A0 B : H →L[ℂ] H) (hA0 : A0.IsPositive) (_hB : IsSelfAdjoint B)
    {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd : 0 < d)
    (hsand : ∀ ρ > 0, ‖invSqrtShift A0 ρ * B * invSqrtShift A0 ρ‖ ≤ d * ρ ^ (a - 2))
    {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : ‖z‖ ≤ deltaA a * lam ^ (2 - a) / d)
    {h : ℝ} (hh : 0 ≤ h) (Cop Fop Hop : H →L[ℂ] H)
    (hCPC : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - z • B), ‖phaseC h w‖ ≤ M) → ‖Cop‖ ≤ (1 + √2) * M)
    (hCPF : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - z • B), ‖phaseF h lam w‖ ≤ M) →
      ‖Fop‖ ≤ (1 + √2) * M)
    (hCPH : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - z • B), ‖phaseH h lam w‖ ≤ M) →
      ‖Hop‖ ≤ (1 + √2) * M)
    (Q' : H →L[ℂ] H) (J : ℝ → H →L[ℂ] H) (hJm : AEStronglyMeasurable J (volume.restrict (Ioi 0)))
    (hJ : ∀ t ∈ Ioi (0 : ℝ),
      ‖J t‖ ≤ ‖z‖ * d / (1 - deltaA a) * (t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2)))
    (hQ' : Q' - 1 = (1 / π) • ∫ t in Ioi (0 : ℝ), J t) :
    (∀ w ∈ numRange (A0 - z • B), PhaseRangeBounds a (deltaA a) lam h w) ∧
      ‖Cop‖ ≤ 3 * Real.exp (lam * h) ∧ ‖Fop‖ ≤ 6 * (1 + lam * h) * Real.exp (lam * h) ∧
      ‖Hop‖ ≤ 6 * Real.exp (lam * h) ∧ ‖Q' - 1‖ ≤ 1 / 6 ∧ IsUnit Q' ∧
      ‖ContinuousLinearMap.adjoint Q'‖ ≤ 7 / 6 ∧
      ‖ContinuousLinearMap.adjoint (Ring.inverse Q')‖ ≤ 6 / 5 ∧
      ∀ u v : H,
        √(‖Cop u + (Fop ∘L ContinuousLinearMap.adjoint Q') v‖ ^ 2 +
            ‖(-(ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Hop)) u +
              (ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Cop ∘L
                ContinuousLinearMap.adjoint Q') v‖ ^ 2) ≤
          100 * Real.exp (2 * (lam * h)) * √(‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
