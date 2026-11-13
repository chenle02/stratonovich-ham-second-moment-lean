/-
Refutation for the standing hypothesis `a < 1` of `L:masked-time-completion`
(`notes/integrated_covariance_foundation.tex` lines 141-152 at a284420), package
theorem `StratonovichHAMSecondMoment.TimeSchur.time_schur_paper` (whose integrability
conclusion `H_a` is built on).

Wrong variant: the hypothesis `a < 1` weakened to `a ≤ 1`, i.e. for every `T > 0` the
integrand `f(t) f(s) |t-s|^{-a}` is integrable on `[0,T]²` for `f ∈ L²(0,T)`.
Counterexample: `a = 1`, `T = 1`, `f = 1`: for every `t ∈ [0,1]`, `s ↦ (s-t)⁻¹` is not
interval integrable on `[0,1]` (`intervalIntegrable_sub_inv_iff`), so no section of
`|t-s|^{-1}` is integrable.  `critical_exponent_contrast` is the package integrability
at `a = 1/2`, the same `T` and `f`.
Junk values: Lean's `0^{-1} = 0` on the diagonal does not matter (null set).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TimeCompletion

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment TimeSchur

namespace Refutations.TimeCompletion

/-- The package integrability at `a = 1/2`, `T = 1`, `f = 1`. -/
theorem critical_exponent_contrast :
    Integrable (fun q : ℝ × ℝ => (fun _ => (1 : ℝ)) q.1 * (fun _ => (1 : ℝ)) q.2 *
        |q.1 - q.2| ^ (-(1 / 2 : ℝ)))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) :=
  (time_schur_paper (by norm_num) (by norm_num) (by norm_num) _ (memLp_const 1)).1

/-- Weakening `a < 1` to `a ≤ 1` is false. -/
theorem critical_exponent_refuted :
    ¬ (∀ a T : ℝ, 0 < a → a ≤ 1 → 0 < T → ∀ f : ℝ → ℝ,
        MemLp f 2 (volume.restrict (Icc 0 T)) →
        Integrable (fun q : ℝ × ℝ => f q.1 * f q.2 * |q.1 - q.2| ^ (-a))
          ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T)))) := by
  intro h
  have hi := h 1 1 (by norm_num) le_rfl (by norm_num) (fun _ => 1) (memLp_const 1)
  have hsec := hi.prod_right_ae
  have hne : volume.restrict (Icc (0 : ℝ) 1) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]; norm_num
  have : (ae (volume.restrict (Icc (0 : ℝ) 1))).NeBot := ae_neBot.2 hne
  obtain ⟨t, ht, hti⟩ := ((ae_restrict_mem measurableSet_Icc).and hsec).exists
  have hII : IntervalIntegrable (fun s : ℝ => (s - t)⁻¹) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    refine (hti.norm).mono' ?_ (ae_of_all _ fun s => ?_)
    · exact ((measurable_id.sub measurable_const).inv).aestronglyMeasurable
    · simp only [one_mul, Real.rpow_neg_one, norm_inv, Real.norm_eq_abs,
        abs_abs, abs_sub_comm s t]
      exact le_rfl
  rw [intervalIntegrable_sub_inv_iff] at hII
  rcases hII with h01 | hnot
  · norm_num at h01
  · exact hnot (by rw [uIcc_of_le zero_le_one]; exact ht)

end Refutations.TimeCompletion
