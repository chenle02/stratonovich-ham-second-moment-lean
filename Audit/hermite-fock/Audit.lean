module

import StratonovichHAMSecondMoment.HermiteFock

set_option autoImplicit false
set_option pp.all true

#check @StratonovichHAMSecondMoment.HermiteFock.deg
#print axioms StratonovichHAMSecondMoment.HermiteFock.deg
#check @StratonovichHAMSecondMoment.HermiteFock.degLE
#print axioms StratonovichHAMSecondMoment.HermiteFock.degLE
#check @StratonovichHAMSecondMoment.HermiteFock.mem_degLE
#print axioms StratonovichHAMSecondMoment.HermiteFock.mem_degLE
#check @StratonovichHAMSecondMoment.HermiteFock.degLE_mono
#print axioms StratonovichHAMSecondMoment.HermiteFock.degLE_mono
#check @StratonovichHAMSecondMoment.HermiteFock.zero_mem_degLE
#print axioms StratonovichHAMSecondMoment.HermiteFock.zero_mem_degLE
#check @StratonovichHAMSecondMoment.HermiteFock.deg_add_unitIdx
#print axioms StratonovichHAMSecondMoment.HermiteFock.deg_add_unitIdx
#check @StratonovichHAMSecondMoment.HermiteFock.sub_add_unitIdx
#print axioms StratonovichHAMSecondMoment.HermiteFock.sub_add_unitIdx
#check @StratonovichHAMSecondMoment.HermiteFock.add_sub_unitIdx
#print axioms StratonovichHAMSecondMoment.HermiteFock.add_sub_unitIdx
#check @StratonovichHAMSecondMoment.HermiteFock.deg_sub_unitIdx
#print axioms StratonovichHAMSecondMoment.HermiteFock.deg_sub_unitIdx
#check @StratonovichHAMSecondMoment.HermiteFock.sub_unitIdx_apply
#print axioms StratonovichHAMSecondMoment.HermiteFock.sub_unitIdx_apply
#check @StratonovichHAMSecondMoment.HermiteFock.add_unitIdx_apply
#print axioms StratonovichHAMSecondMoment.HermiteFock.add_unitIdx_apply
#check @StratonovichHAMSecondMoment.HermiteFock.sum_degLE_succ_eq
#print axioms StratonovichHAMSecondMoment.HermiteFock.sum_degLE_succ_eq
#check @StratonovichHAMSecondMoment.HermiteFock.sum_degLE_eq_of_vanish
#print axioms StratonovichHAMSecondMoment.HermiteFock.sum_degLE_eq_of_vanish
#check @StratonovichHAMSecondMoment.HermiteFock.Supp
#print axioms StratonovichHAMSecondMoment.HermiteFock.Supp
#check @StratonovichHAMSecondMoment.HermiteFock.ann
#print axioms StratonovichHAMSecondMoment.HermiteFock.ann
#check @StratonovichHAMSecondMoment.HermiteFock.cre
#print axioms StratonovichHAMSecondMoment.HermiteFock.cre
#check @StratonovichHAMSecondMoment.HermiteFock.gmul
#print axioms StratonovichHAMSecondMoment.HermiteFock.gmul
#check @StratonovichHAMSecondMoment.HermiteFock.creRow
#print axioms StratonovichHAMSecondMoment.HermiteFock.creRow
#check @StratonovichHAMSecondMoment.HermiteFock.fieldOp
#print axioms StratonovichHAMSecondMoment.HermiteFock.fieldOp
#check @StratonovichHAMSecondMoment.HermiteFock.vac
#print axioms StratonovichHAMSecondMoment.HermiteFock.vac
#check @StratonovichHAMSecondMoment.HermiteFock.cre_of_eq_zero
#print axioms StratonovichHAMSecondMoment.HermiteFock.cre_of_eq_zero
#check @StratonovichHAMSecondMoment.HermiteFock.cre_ann
#print axioms StratonovichHAMSecondMoment.HermiteFock.cre_ann
#check @StratonovichHAMSecondMoment.HermiteFock.number_identity
#print axioms StratonovichHAMSecondMoment.HermiteFock.number_identity
#check @StratonovichHAMSecondMoment.HermiteFock.sum_inner_ann
#print axioms StratonovichHAMSecondMoment.HermiteFock.sum_inner_ann
#check @StratonovichHAMSecondMoment.HermiteFock.sum_inner_cre
#print axioms StratonovichHAMSecondMoment.HermiteFock.sum_inner_cre
#check @StratonovichHAMSecondMoment.HermiteFock.sq_sum_re_inner_le
#print axioms StratonovichHAMSecondMoment.HermiteFock.sq_sum_re_inner_le
#check @StratonovichHAMSecondMoment.HermiteFock.creRow_bound
#print axioms StratonovichHAMSecondMoment.HermiteFock.creRow_bound
#check @StratonovichHAMSecondMoment.HermiteFock.creOp
#print axioms StratonovichHAMSecondMoment.HermiteFock.creOp
#check @StratonovichHAMSecondMoment.HermiteFock.annOp
#print axioms StratonovichHAMSecondMoment.HermiteFock.annOp
#check @StratonovichHAMSecondMoment.HermiteFock.fieldOp_eq
#print axioms StratonovichHAMSecondMoment.HermiteFock.fieldOp_eq
#check @StratonovichHAMSecondMoment.HermiteFock.creOp_bound
#print axioms StratonovichHAMSecondMoment.HermiteFock.creOp_bound
#check @StratonovichHAMSecondMoment.HermiteFock.annOp_bound
#print axioms StratonovichHAMSecondMoment.HermiteFock.annOp_bound
#check @StratonovichHAMSecondMoment.HermiteFock.annOp_supp
#print axioms StratonovichHAMSecondMoment.HermiteFock.annOp_supp
#check @StratonovichHAMSecondMoment.HermiteFock.fieldOp_supp
#print axioms StratonovichHAMSecondMoment.HermiteFock.fieldOp_supp
#check @StratonovichHAMSecondMoment.HermiteFock.fieldOp_bound
#print axioms StratonovichHAMSecondMoment.HermiteFock.fieldOp_bound
#check @StratonovichHAMSecondMoment.HermiteFock.fieldOp_bound_trunc
#print axioms StratonovichHAMSecondMoment.HermiteFock.fieldOp_bound_trunc
#check @StratonovichHAMSecondMoment.HermiteFock.fieldOp_symm_trunc
#print axioms StratonovichHAMSecondMoment.HermiteFock.fieldOp_symm_trunc
#check @StratonovichHAMSecondMoment.HermiteFock.creRow_attained
#print axioms StratonovichHAMSecondMoment.HermiteFock.creRow_attained
#check @StratonovichHAMSecondMoment.HermiteFock.integral_norm_sq_sum_smul
#print axioms StratonovichHAMSecondMoment.HermiteFock.integral_norm_sq_sum_smul
#check @StratonovichHAMSecondMoment.HermiteFock.iota
#print axioms StratonovichHAMSecondMoment.HermiteFock.iota
#check @StratonovichHAMSecondMoment.HermiteFock.integral_norm_sq_iota
#print axioms StratonovichHAMSecondMoment.HermiteFock.integral_norm_sq_iota
#check @StratonovichHAMSecondMoment.HermiteFock.iota_vac
#print axioms StratonovichHAMSecondMoment.HermiteFock.iota_vac
#check @StratonovichHAMSecondMoment.HermiteFock.coord_smul_iota
#print axioms StratonovichHAMSecondMoment.HermiteFock.coord_smul_iota
#check @StratonovichHAMSecondMoment.HermiteFock.sum_coord_smul_iota
#print axioms StratonovichHAMSecondMoment.HermiteFock.sum_coord_smul_iota
#check @StratonovichHAMSecondMoment.HermiteFock.gaussian_field_bound
#print axioms StratonovichHAMSecondMoment.HermiteFock.gaussian_field_bound
#check @StratonovichHAMSecondMoment.HermiteFock.gaussian_field_bound_trunc
#print axioms StratonovichHAMSecondMoment.HermiteFock.gaussian_field_bound_trunc
#check @StratonovichHAMSecondMoment.HermiteFock.vacuum_insertion_isometry
#print axioms StratonovichHAMSecondMoment.HermiteFock.vacuum_insertion_isometry

open MeasureTheory ProbabilityTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.HermiteFock

open StratonovichHAMSecondMoment.HermiteFock

/-- Consumer: with a single self-adjoint mode `H = id` (column constant `1`), the
Gaussian field `x_0 · F` of a degree-`≤ 1` expansion has `L²` norm at most
`2√2` times that of `F`. -/
private theorem audit_consumer (v : (Fin 1 → ℕ) → ℂ) (hv : Supp 1 v) :
    ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • (ContinuousLinearMap.id ℂ ℂ) (iota 1 v x)‖ ^ 2
        ∂GaussianIBP.stdPi 1 ≤
      (2 * Real.sqrt (((1 : ℕ) : ℝ) + 1) * Real.sqrt 1) ^ 2 *
        ∫ x, ‖iota 1 v x‖ ^ 2 ∂GaussianIBP.stdPi 1 :=
  (gaussian_field_bound 1 (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun _ _ _ => rfl)
    zero_le_one (fun u => by simp) hv).2.2

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.HermiteFock
