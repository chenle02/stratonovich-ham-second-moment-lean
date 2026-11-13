module
import StratonovichHAMSecondMoment.OccupationKernelRow
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.OccupationKernelRow.kstarIntegrand
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.kstarIntegrand
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar
#check @StratonovichHAMSecondMoment.OccupationKernelRow.row
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.row
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Rstar
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Rstar
#check @StratonovichHAMSecondMoment.OccupationKernelRow.kstarIntegrand_eq_psiKernel
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.kstarIntegrand_eq_psiKernel
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_eq_Psi
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_eq_Psi
#check @StratonovichHAMSecondMoment.OccupationKernelRow.kstarIntegrand_integrable
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.kstarIntegrand_integrable
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_neg
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_neg
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_pos
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_pos
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_nonneg
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_nonneg
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_le_rpow
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_le_rpow
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Psi_diag_strictAnti
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Psi_diag_strictAnti
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_strictAntiOn
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_strictAntiOn
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_measurable
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_measurable
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_intervalIntegrable_zero_of_nonneg
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_intervalIntegrable_zero_of_nonneg
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_intervalIntegrable
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_intervalIntegrable
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_locallyIntegrable
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_locallyIntegrable
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Phi
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Phi
#check @StratonovichHAMSecondMoment.OccupationKernelRow.row_eq_Phi
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.row_eq_Phi
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Phi_sum_le_of_le_half
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Phi_sum_le_of_le_half
#check @StratonovichHAMSecondMoment.OccupationKernelRow.Phi_sum_le
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.Phi_sum_le
#check @StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row
#check @StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row_paper
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row_paper
#check @StratonovichHAMSecondMoment.OccupationKernelRow.pairMeasure
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.pairMeasure
#check @StratonovichHAMSecondMoment.OccupationKernelRow.pairing
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.pairing
#check @StratonovichHAMSecondMoment.OccupationKernelRow.ae_pair_of_ae
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.ae_pair_of_ae
#check @StratonovichHAMSecondMoment.OccupationKernelRow.spatial_physical_pair
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.spatial_physical_pair
#check @StratonovichHAMSecondMoment.OccupationKernelRow.spatial_physical_pair_paper
#print axioms StratonovichHAMSecondMoment.OccupationKernelRow.spatial_physical_pair_paper
open MeasureTheory Set StratonovichHAMSecondMoment.HomogHypothesis in
/-- Consumer: under the section's standing assumptions, every row value on `[0,1]` is at
most `R_⋆`, the maximum is attained at `s = 1/2`, and `0 < R_⋆`. -/
private theorem row_bound_consumer {d : ℕ} {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) :
    (∀ s ∈ Icc (0 : ℝ) 1,
      StratonovichHAMSecondMoment.OccupationKernelRow.row a ((4 - alpha) - 2 * a) s ≤
        StratonovichHAMSecondMoment.OccupationKernelRow.Rstar a ((4 - alpha) - 2 * a)) ∧
    StratonovichHAMSecondMoment.OccupationKernelRow.row a ((4 - alpha) - 2 * a) (1 / 2) =
      StratonovichHAMSecondMoment.OccupationKernelRow.Rstar a ((4 - alpha) - 2 * a) ∧
    0 < StratonovichHAMSecondMoment.OccupationKernelRow.Rstar a ((4 - alpha) - 2 * a) := by
  obtain ⟨-, -, -, -, -, -, hG, -, hpos⟩ :=
    StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row_paper hH hΓ _ rfl
  refine ⟨fun s hs => hG.2 ⟨s, hs, rfl⟩, ?_, hpos⟩
  have h1 := StratonovichHAMSecondMoment.OccupationKernelRow.row_eq_Phi a ((4 - alpha) - 2 * a)
    (1 / 2) hH.alpha0_pos hH.alpha0_lt_one (by linarith [hH.threshold, hH.alpha0_lt_one])
  rw [h1, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  simp only [StratonovichHAMSecondMoment.OccupationKernelRow.Rstar,
    StratonovichHAMSecondMoment.OccupationKernelRow.Phi]
  ring
#check @row_bound_consumer
#print axioms row_bound_consumer
open MeasureTheory Set StratonovichHAMSecondMoment.HomogHypothesis in
/-- Consumer: under the standing assumptions the pairing `B_Γ` is well defined on
Lebesgue classes. -/
private theorem pairing_class_consumer {d : ℕ} {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) (f f' : Rd d → ENNReal)
    (hf : f =ᵐ[volume] f') :
    StratonovichHAMSecondMoment.OccupationKernelRow.pairing Γ f f =
      StratonovichHAMSecondMoment.OccupationKernelRow.pairing Γ f' f' :=
  (StratonovichHAMSecondMoment.OccupationKernelRow.spatial_physical_pair_paper hH hΓ).2.1
    f f' f f' hf hf
#check @pairing_class_consumer
#print axioms pairing_class_consumer
example : 0 < StratonovichHAMSecondMoment.OccupationKernelRow.Rstar (1 / 2) 1 :=
  (StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row (1 / 2) 1
    (by norm_num) (by norm_num) one_pos).2.2.2.2.2.2.2.2
example : StratonovichHAMSecondMoment.OccupationKernelRow.Kstar (1 / 2) 1 1 ≤
    |(1 : ℝ)| ^ (-(1 / 2 : ℝ)) :=
  StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_le_rpow _ _ _ (by norm_num) one_pos
    one_ne_zero
