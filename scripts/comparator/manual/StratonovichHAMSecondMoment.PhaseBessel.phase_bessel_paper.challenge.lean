namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseBessel
open MeasureTheory ComplexConjugate
universe u_5
-- Statement copied from the source (the printed type round-trips only up to definitional equality (`EuclideanSpace` printed as `WithLp 2 ..`); `Type*` written as `Type u_5`, the project's universe name).
/-- H separable (unused) complete complex inner product space, u : Fin K -> Fin 2 -> R^d -> C orthonormal for Lebesgue, g j in L^2: both coefficient integrands and sum_j norm(g j)^2 integrable; E:phase-bessel and its conjugated version hold. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PhaseBessel.phase_bessel_paper {d K : ℕ}
    {H : Type u_5} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (_hsep : TopologicalSpace.SeparableSpace H)
    {u : Fin K → Fin 2 → EuclideanSpace ℝ (Fin d) → ℂ}
    {g : Fin 2 → EuclideanSpace ℝ (Fin d) → H}
    (hu : IsOrthonormalL2 volume u) (hg : ∀ j, MemLp (g j) 2 volume) :
    (∀ k, Integrable (fun η => ∑ j, u k j η • g j η)) ∧
      (∀ k, Integrable (fun η => ∑ j, conj (u k j η) • g j η)) ∧
      Integrable (fun η => ∑ j, ‖g j η‖ ^ 2) ∧
      ∑ k, ‖∫ η, ∑ j, u k j η • g j η‖ ^ 2 ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 ∧
      ∑ k, ‖∫ η, ∑ j, conj (u k j η) • g j η‖ ^ 2 ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseBessel
