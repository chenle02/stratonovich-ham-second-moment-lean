namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)
open SpatialFourLinear (IsH1Pair H1Tendsto)
open OccupationPhysicalClass (volI sqPair IsOccField)
open VariationalDilation (CPos rawCost)
variable {d : ℕ}
/-- HomogCovariance, Gamma != 0: Q with <Q f, Q h> = B_Gamma(f^2,h^2) < inf, |Q f|^2 = A_sp(f), sequential continuity, a.e. invariance; on IsOccField G DG: Q(g_s) in L^2(I;H_sp), |rho_g|^2 = A(g), the polarized, bound and mean identities. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.occupation_raw_square_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    (∀ (f h : Rd d → ℝ) (g k : Rd d → Rd d), IsH1Pair f g → IsH1Pair h k →
      sqPair Γ f h < ⊤ ∧
      ⟪Q (SpData.ofHomog hH) f, Q (SpData.ofHomog hH) h⟫ = (sqPair Γ f h).toReal) ∧
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g →
      ‖Q (SpData.ofHomog hH) f‖ ^ 2 = (sqPair Γ f f).toReal) ∧
    (∀ (u : ℕ → Rd d → ℝ) (v : ℕ → Rd d → Rd d) (f : Rd d → ℝ) (g : Rd d → Rd d),
      (∀ n, IsH1Pair (u n) (v n)) → IsH1Pair f g → H1Tendsto u v f g →
      Tendsto (fun n => Q (SpData.ofHomog hH) (u n)) atTop (𝓝 (Q (SpData.ofHomog hH) f))) ∧
    (∀ (f f' : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g → f =ᵐ[volume] f' →
      Q (SpData.ofHomog hH) f' = Q (SpData.ofHomog hH) f) ∧
    ∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG →
      MemLp (sqField (SpData.ofHomog hH) G) 2 volI ∧
      ‖rho (TParams.ofHomog hH) (SpData.ofHomog hH) G‖ ^ 2 =
        RawOccupationEnergy.A alpha0 Γ G ∧
      ∀ Ψ ∈ CPos d,
        ⟪incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ,
          rho (TParams.ofHomog hH) (SpData.ofHomog hH) G⟫ =
          ∫ q, kern alpha0 (q.1 - q.2) *
            testSqPair (SpData.ofHomog hH) (fun x => Ψ (q.1, x)) (G q.2)
            ∂(timeMeasure.prod timeMeasure) ∧
        ⟪incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ,
          rho (TParams.ofHomog hH) (SpData.ofHomog hH) G⟫ ≤
          Real.sqrt (rawCost alpha0 Γ Ψ * RawOccupationEnergy.A alpha0 Γ G) ∧
        (∀ᵐ s ∂volI, Integrable fun x => VariationalDilation.mean alpha0 Γ Ψ s x * G s x ^ 2) ∧
        IntegrableOn (fun s => ∫ x, VariationalDilation.mean alpha0 Γ Ψ s x * G s x ^ 2)
          (Ioo (0 : ℝ) 1) ∧
        ⟪incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ,
          rho (TParams.ofHomog hH) (SpData.ofHomog hH) G⟫ =
          ∫ s in Ioo (0 : ℝ) 1, ∫ x, VariationalDilation.mean alpha0 Γ Ψ s x * G s x ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
