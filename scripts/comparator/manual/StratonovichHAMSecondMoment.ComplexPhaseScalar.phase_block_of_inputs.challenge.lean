namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
open Real Set MeasureTheory Filter Topology
open StratonovichHAMSecondMoment.StaticPhaseCauchy
-- Statement copied from the source (the printed type elaborates the semiring structure of `ℂ` as `Complex.instSemiring`, the declaration through `RCLike`).
-- The section variables and scoped opens of the source, as there:
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- If PhaseRangeBounds a (deltaA a) lam h holds on numRange L, Cop, Fop, Hop satisfy Crouzeix-Palencia hypotheses on numRange L and Q' - 1 = (1/pi) int J with ||J t|| dominated, then the operator bounds, ||Q' - 1|| <= 1/6, Q' a unit, the Neumann bounds and the block bound. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ComplexPhaseScalar.phase_block_of_inputs {a lam h c : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hlam : 0 < lam)
    (hh : 0 ≤ h) (hcδ : c * lam ^ (a - 2) ≤ deltaA a) (L : H →L[ℂ] H)
    (hrange : ∀ w ∈ numRange L, PhaseRangeBounds a (deltaA a) lam h w)
    (Cop Fop Hop : H →L[ℂ] H)
    (hCPC : ∀ M ≥ 0, (∀ w ∈ numRange L, ‖phaseC h w‖ ≤ M) → ‖Cop‖ ≤ (1 + √2) * M)
    (hCPF : ∀ M ≥ 0, (∀ w ∈ numRange L, ‖phaseF h lam w‖ ≤ M) → ‖Fop‖ ≤ (1 + √2) * M)
    (hCPH : ∀ M ≥ 0, (∀ w ∈ numRange L, ‖phaseH h lam w‖ ≤ M) → ‖Hop‖ ≤ (1 + √2) * M)
    (Q' : H →L[ℂ] H) (J : ℝ → H →L[ℂ] H) (hJm : AEStronglyMeasurable J (volume.restrict (Ioi 0)))
    (hJ : ∀ t ∈ Ioi (0 : ℝ),
      ‖J t‖ ≤ c / (1 - deltaA a) * (t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2)))
    (hQ' : Q' - 1 = (1 / π) • ∫ t in Ioi (0 : ℝ), J t) :
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
