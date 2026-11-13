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
/-- If l > 0, the map (s,x) -> (s, l x) is quasi-measure-preserving for volI x volume on R x R^d (volI is Lebesgue measure on (0,1)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RawOccupationEnergy.qmp_dil {ℓ : ℝ} (hℓ : 0 < ℓ) :
    QuasiMeasurePreserving (Prod.map (id : ℝ → ℝ) (fun x : Rd d => ℓ • x))
      (volI.prod (volume : Measure (Rd d))) (volI.prod (volume : Measure (Rd d))) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.RawOccupationEnergy.qmp_dil
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy
