module

import StratonovichHAMSecondMoment.D1Upper

set_option autoImplicit false
set_option pp.all true

#check @StratonovichHAMSecondMoment.D1Upper.Ksp_nonneg
#print axioms StratonovichHAMSecondMoment.D1Upper.Ksp_nonneg
#check @StratonovichHAMSecondMoment.D1Upper.card_mul_lintegral_twoSimplex_le
#print axioms StratonovichHAMSecondMoment.D1Upper.card_mul_lintegral_twoSimplex_le
#check @StratonovichHAMSecondMoment.D1Upper.timeSum_comp_perm
#print axioms StratonovichHAMSecondMoment.D1Upper.timeSum_comp_perm
#check @StratonovichHAMSecondMoment.D1Upper.lintegral_cube_timeWeight
#print axioms StratonovichHAMSecondMoment.D1Upper.lintegral_cube_timeWeight
#check @StratonovichHAMSecondMoment.D1Upper.factorial_rpow_le
#print axioms StratonovichHAMSecondMoment.D1Upper.factorial_rpow_le
#check @StratonovichHAMSecondMoment.D1Upper.div_le_div_factorial
#print axioms StratonovichHAMSecondMoment.D1Upper.div_le_div_factorial
#check @StratonovichHAMSecondMoment.D1Upper.coeffA_le_of_spatial
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffA_le_of_spatial
#check @StratonovichHAMSecondMoment.D1Upper.coeffA_riesz_le
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffA_riesz_le
#check @StratonovichHAMSecondMoment.D1Upper.coeffA_white_le
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffA_white_le
#check @StratonovichHAMSecondMoment.D1Upper.coeffA_riesz_le_factorial
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffA_riesz_le_factorial
#check @StratonovichHAMSecondMoment.D1Upper.coeffA_white_le_factorial
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffA_white_le_factorial
#check @StratonovichHAMSecondMoment.D1Upper.DiagramLimits
#print axioms StratonovichHAMSecondMoment.D1Upper.DiagramLimits
#check @StratonovichHAMSecondMoment.D1Upper.diagramLimits_of_mixedMoment
#print axioms StratonovichHAMSecondMoment.D1Upper.diagramLimits_of_mixedMoment
#check @StratonovichHAMSecondMoment.D1Upper.coeffALim_le_of_forall
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffALim_le_of_forall
#check @StratonovichHAMSecondMoment.D1Upper.coeffALim_riesz_le
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffALim_riesz_le
#check @StratonovichHAMSecondMoment.D1Upper.coeffALim_white_le
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffALim_white_le
#check @StratonovichHAMSecondMoment.D1Upper.pow_mul_rpow_eq
#print axioms StratonovichHAMSecondMoment.D1Upper.pow_mul_rpow_eq
#check @StratonovichHAMSecondMoment.D1Upper.secondMoment_le_of_coeff
#print axioms StratonovichHAMSecondMoment.D1Upper.secondMoment_le_of_coeff
#check @StratonovichHAMSecondMoment.D1Upper.secondMoment_riesz_le
#print axioms StratonovichHAMSecondMoment.D1Upper.secondMoment_riesz_le
#check @StratonovichHAMSecondMoment.D1Upper.secondMoment_white_le
#print axioms StratonovichHAMSecondMoment.D1Upper.secondMoment_white_le
#check @StratonovichHAMSecondMoment.D1Upper.d1_upper_paper_riesz
#print axioms StratonovichHAMSecondMoment.D1Upper.d1_upper_paper_riesz
#check @StratonovichHAMSecondMoment.D1Upper.d1_upper_paper_white
#print axioms StratonovichHAMSecondMoment.D1Upper.d1_upper_paper_white
#check @StratonovichHAMSecondMoment.D1Upper.covEps_smul
#print axioms StratonovichHAMSecondMoment.D1Upper.covEps_smul
#check @StratonovichHAMSecondMoment.D1Upper.diagram_const_mul
#print axioms StratonovichHAMSecondMoment.D1Upper.diagram_const_mul
#check @StratonovichHAMSecondMoment.D1Upper.diagramLimits_white
#print axioms StratonovichHAMSecondMoment.D1Upper.diagramLimits_white
#check @StratonovichHAMSecondMoment.D1Upper.coeffALim_white_le'
#print axioms StratonovichHAMSecondMoment.D1Upper.coeffALim_white_le'
#check @StratonovichHAMSecondMoment.D1Upper.d1_upper_paper_white'
#print axioms StratonovichHAMSecondMoment.D1Upper.d1_upper_paper_white'

set_option pp.all false

-- Consumer: the TeX's coefficient display and moment display for the Riesz
-- case, read off the paper wrapper under the supplied input `MixedMoment`.
open MeasureTheory StratonovichHAMSecondMoment DiagramModel D1Upper TwoSimplexTime in
theorem audit_consumer {c α α₀ t : ℝ} (hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ}
    (h : MixedMoment 1 α₀ (volume.withDensity (HigherRieszTwo.riesz c α)) P X u t) :
    ∑ m ∈ Finset.range (2 * 1 + 1), ∫ ω, X m ω * X (2 * 1 - m) ω ∂P ≤
        (2 * Zc α₀ * D1Spatial.Ksp c α) ^ 1 * t ^ ((4 - α - α₀) * 1) /
          ((Nat.factorial 1 : ℝ) * (1 : ℝ) ^ ((2 - α) * 1)) ∧
      ∫ ω, u ω ^ 2 ∂P ≤ Real.exp ((3 - α) * (2 * Zc α₀ * D1Spatial.Ksp c α) ^ (1 / (3 - α)) *
        t ^ ((4 - α - α₀) / (3 - α))) := by
  have H := d1_upper_paper_riesz hα₀0 hα₀1 hc hα0 hα1 ht h
  have := (H.2.1 1 le_rfl).1
  push_cast at this ⊢
  exact ⟨this, H.2.2⟩

#print axioms audit_consumer
