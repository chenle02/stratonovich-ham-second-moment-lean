namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open HomogHypothesis (Rd HomogCovariance)
variable {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E]
/-- For a second countable normed group E, an s-finite nu on R and G a.e.-strongly measurable on nu x Lebesgue with G(s, .) in L^2 for nu-a.e. s: s -> [G(s, .)] has an a.e.-strongly measurable L^2-valued version. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ClassOBridge.exists_aesm_of_joint [SecondCountableTopology E] {ν : Measure ℝ} [SFinite ν]
    {G : ℝ × Rd d → E}
    (hG : AEStronglyMeasurable G (ν.prod volume))
    (hL : ∀ᵐ s ∂ν, MemLp (fun x => G (s, x)) 2 volume) :
    ∃ F : ℝ → Lp E 2 (volume : Measure (Rd d)), AEStronglyMeasurable F ν ∧
      ∀ᵐ s ∂ν, (F s : Rd d → E) =ᵐ[volume] fun x => G (s, x) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge
