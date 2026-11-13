module
import StratonovichHAMSecondMoment.RawOccupationEnergy
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.Araw
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.Araw
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.A
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.A
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.energySet
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.energySet
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.EO
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.EO
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.kern_meas
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.kern_meas
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.Araw_le
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.Araw_le
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.raw_occupation_bound
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.raw_occupation_bound
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.T_pos
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.T_pos
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.one_le_kern
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.one_le_kern
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.exists_pos_member
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.exists_pos_member
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.dilField
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.dilField
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.dilGrad
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.dilGrad
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.lintegral_comp_smul_rd
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.lintegral_comp_smul_rd
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.map_pairMeasure
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.map_pairMeasure
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.sqPair_dil
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.sqPair_dil
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.gradSqE_dil
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.gradSqE_dil
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.qmp_dil
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.qmp_dil
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.isOccField_dil
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.isOccField_dil
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.Araw_dil
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.Araw_dil
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.dil_inv
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.dil_inv
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.scalar_max_zeta
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.scalar_max_zeta
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.scalar_attain_zeta
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.scalar_attain_zeta
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.raw_occupation_energy
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.raw_occupation_energy
#check @StratonovichHAMSecondMoment.RawOccupationEnergy.raw_occupation_energy_paper
#print axioms StratonovichHAMSecondMoment.RawOccupationEnergy.raw_occupation_energy_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.RawOccupationEnergy

open StratonovichHAMSecondMoment.RawOccupationEnergy

/-- Consumer of the wrapper: under `H:homog` and `Γ ≠ 0`, `C_occ` is positive and
`𝓔_{1/2}^𝒪 = D_{1/2} C_occ^{2/(2-α)}` is positive. -/
private theorem audit_consumer {d : ℕ} {alpha a : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) :
    0 < Cocc a alpha Γ ∧
      EO a Γ (1 / 2) = SpatialBracket.Dzeta alpha (1 / 2) * Cocc a alpha Γ ^ (2 / (2 - alpha)) ∧
      0 < EO a Γ (1 / 2) := by
  obtain ⟨-, -, h3, -, -, h6⟩ := raw_occupation_energy_paper h hΓ
  obtain ⟨-, -, e, -, p, -⟩ := h6 (1 / 2) (by norm_num)
  exact ⟨h3, e, p⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.RawOccupationEnergy
