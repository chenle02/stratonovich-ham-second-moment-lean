/-
Refutation for the `L^2(0,1)` part of `L:temporal-equilibrium` (TeX lines 42
and 85), package theorem
`StratonovichHAMSecondMoment.TemporalEquilibrium.density_sq_integrableOn`
and package definition
`StratonovichHAMSecondMoment.TemporalEquilibrium.density`.

Wrong variant: the hypothesis `a > 0` dropped. At a = 0 the package density is
the arcsine density f_0(t) = [t(1-t)]^{-1/2}/(Γ(1/2)Γ(1/2)), and
f_0² = 1/(π² t(1-t)) is not integrable on (0,1) (it dominates 1/(π² t)).
`density_zero_sq_not_integrableOn` is the pointwise statement at a = 0 (as
before); `l2_fails_without_pos` states the dropped-hypothesis variant of
`density_sq_integrableOn` (only `a < 1` kept) and follows from it.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TemporalEquilibrium

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.TemporalEquilibrium

/-- The square of the package density at `a = 0` is not integrable on `(0,1)`. -/
theorem density_zero_sq_not_integrableOn :
    ¬ IntegrableOn
      (fun t => StratonovichHAMSecondMoment.TemporalEquilibrium.density 0 t ^ 2) (Ioo 0 1) := by
  intro h
  have hG : Gamma ((1 - 0) / 2) * Gamma (1 - (1 - 0) / 2) = π := by
    norm_num [Gamma_one_half_eq, mul_self_sqrt pi_pos.le]
  have hpi : 0 < π := pi_pos
  have h2 : IntegrableOn (fun t => π ^ 2 *
      StratonovichHAMSecondMoment.TemporalEquilibrium.density 0 t ^ 2) (Ioo 0 1) :=
    h.const_mul _
  have hbad : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 1) := by
    refine Integrable.mono' h2 ((continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt hx.1))).aestronglyMeasurable measurableSet_Ioo) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 := ht.1
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    have hp : 0 < t * (1 - t) := mul_pos ht0 ht1
    have hsq : ((t * (1 - t)) ^ (-((1 - 0) / 2) : ℝ)) ^ 2 = (t * (1 - t))⁻¹ := by
      rw [← rpow_natCast, ← rpow_mul hp.le]; norm_num; rw [rpow_neg_one, mul_inv, mul_comm]
    rw [norm_of_nonneg (rpow_nonneg ht0.le _),
      StratonovichHAMSecondMoment.TemporalEquilibrium.density, hG, div_pow, hsq,
      mul_div_cancel₀ _ (by positivity), rpow_neg_one, inv_le_inv₀ ht0 hp]
    nlinarith
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff one_pos] at hbad
  norm_num at hbad

/-- `density_sq_integrableOn` fails without its hypothesis `0 < a`. -/
theorem l2_fails_without_pos :
    ¬ ∀ a : ℝ, a < 1 → IntegrableOn
      (fun t => StratonovichHAMSecondMoment.TemporalEquilibrium.density a t ^ 2) (Ioo 0 1) :=
  fun h => density_zero_sq_not_integrableOn (h 0 one_pos)

end Refutations.TemporalEquilibrium
