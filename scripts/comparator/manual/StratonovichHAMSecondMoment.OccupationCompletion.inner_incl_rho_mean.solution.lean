namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)
open WeakSobolev (IsTestFunction)
open SpatialFourLinear (IsH1Pair SquareBound)
open OccupationPhysicalClass (volI IsOccField SquarePairingBounds)
open OccupationKernelRow (pairMeasure)
open VariationalDilation (CPos mean conv)
variable {d : ℕ}
variable {S : SpData d}
variable {p : TParams}
/-- SquareBound and SquarePairingBounds; R >= 0; 0 < alpha < 2; IsOccField G DG; Psi in C_pos: x |-> h_(Psi,s) g_s^2 integrable for a.e. s, s |-> int h g_s^2 integrable on (0,1), <Psi, rho_g> = int_I int h_(Psi,s) g_s^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.inner_incl_rho_mean {alpha R : ℝ} (hB : SquareBound S.Γ alpha R)
    (hSPB : SquarePairingBounds S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    (∀ᵐ s ∂volI, Integrable fun x => mean p.a S.Γ Ψ s x * G s x ^ 2) ∧
      IntegrableOn (fun s => ∫ x, mean p.a S.Γ Ψ s x * G s x ^ 2) (Ioo (0 : ℝ) 1) ∧
      ⟪incl p S Ψ, rho p S G⟫ = ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean p.a S.Γ Ψ s x * G s x ^ 2 := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.OccupationCompletion.inner_incl_rho_mean
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
