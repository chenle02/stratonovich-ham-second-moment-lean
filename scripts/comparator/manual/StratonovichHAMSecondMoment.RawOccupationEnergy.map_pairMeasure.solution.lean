namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy
open MeasureTheory Set Real Filter
open scoped ENNReal
open HomogHypothesis (Rd HomogCovariance)
open OccupationPhysicalClass (volI sqPair gradSqE Tlin T IsOccField SquarePairingBounds)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open OccupationCeilingFinite (K0)
open SpatialStaticControls (IsUnitH1)
open SpatialBracket (Dzeta)
-- Statement copied from the source (the printed type elaborates the measurable space on `Rd d` as `WithLp.measurableSpace`, the declaration through `MeasureSpace.toMeasurableSpace`).
-- The section variables and scoped opens of the source, as there:
variable {d : ℕ}
/-- If Gamma is s-finite with SetScaling alpha Gamma and l > 0, the pushforward of volume x Gamma under (x,y) -> (l x, l y) is (ofReal((l^d)^(-1)) * ofReal(l^(alpha - d))) times volume x Gamma. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RawOccupationEnergy.map_pairMeasure {alpha : ℝ} {Γ : Measure (Rd d)} [SFinite Γ]
    (hS : VariationalDilation.SetScaling alpha Γ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Measure.map (Prod.map (fun x : Rd d => ℓ • x) (fun y : Rd d => ℓ • y))
        ((volume : Measure (Rd d)).prod Γ) =
      (ENNReal.ofReal ((ℓ ^ d)⁻¹) * ENNReal.ofReal (ℓ ^ (alpha - d))) •
        ((volume : Measure (Rd d)).prod Γ) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.RawOccupationEnergy.map_pairMeasure
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy
