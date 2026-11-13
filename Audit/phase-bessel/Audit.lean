module
import StratonovichHAMSecondMoment.PhaseBessel
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.PhaseBessel.IsOrthonormalL2
#print axioms StratonovichHAMSecondMoment.PhaseBessel.IsOrthonormalL2
#check @StratonovichHAMSecondMoment.PhaseBessel.coeff
#print axioms StratonovichHAMSecondMoment.PhaseBessel.coeff
#check @StratonovichHAMSecondMoment.PhaseBessel.memLp_conj
#print axioms StratonovichHAMSecondMoment.PhaseBessel.memLp_conj
#check @StratonovichHAMSecondMoment.PhaseBessel.integrable_mul_of_memLp
#print axioms StratonovichHAMSecondMoment.PhaseBessel.integrable_mul_of_memLp
#check @StratonovichHAMSecondMoment.PhaseBessel.integrable_smul_of_memLp
#print axioms StratonovichHAMSecondMoment.PhaseBessel.integrable_smul_of_memLp
#check @StratonovichHAMSecondMoment.PhaseBessel.integrable_coeff_integrand
#print axioms StratonovichHAMSecondMoment.PhaseBessel.integrable_coeff_integrand
#check @StratonovichHAMSecondMoment.PhaseBessel.integrable_sum_norm_sq
#print axioms StratonovichHAMSecondMoment.PhaseBessel.integrable_sum_norm_sq
#check @StratonovichHAMSecondMoment.PhaseBessel.residual_expand
#print axioms StratonovichHAMSecondMoment.PhaseBessel.residual_expand
#check @StratonovichHAMSecondMoment.PhaseBessel.phase_bessel
#print axioms StratonovichHAMSecondMoment.PhaseBessel.phase_bessel
#check @StratonovichHAMSecondMoment.PhaseBessel.isOrthonormalL2_conj
#print axioms StratonovichHAMSecondMoment.PhaseBessel.isOrthonormalL2_conj
#check @StratonovichHAMSecondMoment.PhaseBessel.phase_bessel_conj
#print axioms StratonovichHAMSecondMoment.PhaseBessel.phase_bessel_conj
#check @StratonovichHAMSecondMoment.PhaseBessel.phase_bessel_paper
#print axioms StratonovichHAMSecondMoment.PhaseBessel.phase_bessel_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.PhaseBessel

open StratonovichHAMSecondMoment.PhaseBessel

/-- Consumer of the wrapper: for an orthonormal family in `L²(ℝ^d; ℂ²)` and
`g ∈ L²(ℝ^d; H²)` with `H` separable, every single coefficient satisfies
`‖∫ ∑ j, u k j • g j‖² ≤ ∫ ∑ j, ‖g j‖²`. -/
private theorem audit_consumer {d K : ℕ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [hsep : TopologicalSpace.SeparableSpace H]
    {u : Fin K → Fin 2 → EuclideanSpace ℝ (Fin d) → ℂ}
    {g : Fin 2 → EuclideanSpace ℝ (Fin d) → H}
    (hu : IsOrthonormalL2 volume u) (hg : ∀ j, MemLp (g j) 2 volume) (k : Fin K) :
    ‖∫ η, ∑ j, u k j η • g j η‖ ^ 2 ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 :=
  le_trans (Finset.single_le_sum (f := fun k => ‖∫ η, ∑ j, u k j η • g j η‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ k))
    (phase_bessel_paper hsep hu hg).2.2.2.1

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.PhaseBessel
