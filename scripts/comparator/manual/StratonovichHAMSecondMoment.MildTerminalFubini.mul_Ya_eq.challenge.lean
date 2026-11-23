-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2 chainWeightReal)
open TerminalWickInputs
open SourceInterface
open MildInterface
variable {d : ℕ}
variable {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}
variable (hc : ∀ w w' : PosW, Continuous fun pq : (↥(Ici (0 : ℝ)) × Rd d) ×
  (↥(Ici (0 : ℝ)) × Rd d) => srcCov α₀ Γ (pq.1, w) (pq.2, w'))
include hc
/-- Given hc (covariance continuity at fixed widths), a source field, finite P, s >= 0, y, widths b (m vertices), a: W(s,y,a) Y_m^b(s,y) is in L^2 and mulL2 W(s,y,a) Y_m^b(s,y) = int prodL2(attach (snoc b a) (snoc z (s,y))) dg_m^(s,y)(z). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildTerminalFubini.mul_Ya_eq (hW : SourceField α₀ Γ P W) [IsFiniteMeasure P] {s : ℝ} (hs : 0 ≤ s)
    (y : Rd d) {m : ℕ} (b : Fin m → PosW) (a : PosW) :
    MemLp (fun ω => fieldL2 hW ((⟨s, hs⟩, y), a) ω * Ya hW s hs y b ω) 2 P ∧
      mulL2 (fieldL2 hW ((⟨s, hs⟩, y), a)) (Ya hW s hs y b) =
        ∫ z, prodL2 hW (attach (Fin.snoc b a : Fin (m + 1) → PosW)
          (Fin.snoc z (termPt hs y) : Fin (m + 1) → Pt d s)) ∂chainMeasure d m s hs y := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
