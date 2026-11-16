/-
Refutation for the absolute convergence in `E:positive-bochner-inclusion`, package theorem
`StratonovichHAMSecondMoment.OccupationCompletion.kform_integrable` (the integrand
`|s-t|^{-a} ⟨F(s), F'(t)⟩` is integrable on `I²` for `0 ≤ a < 1`, `F, F' ∈ L²(I; G)`;
`L:positive-raw-embedding`, `integrated_intrinsic_constant.tex` lines 27-31 and 52-57 at
39f2597a, where `a = α₀ < 1`).

Wrong variant (class (c), a broader Lean generalization outside the manuscript domain): the
hypothesis `a < 1` dropped.  Counterexample: `a = 1`, `G = ℝ`, `F = F' = 1`: the integrand is
`|s-t|^{-1}`, and if it were integrable on `(0,1)²` then for a.e. `s` the section
`t ↦ (t-s)⁻¹` would be integrable on `(s,1)`, which `intervalIntegrable_sub_inv_iff` excludes.
No junk-value reliance.  `drop_a_lt_one_contrast` is the package theorem at `a = 1/2`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationCompletion

set_option autoImplicit false

open MeasureTheory Set
open scoped RealInnerProductSpace
open StratonovichHAMSecondMoment SpaceTimePositivity TimeSchur OccupationCompletion

namespace Refutations.OccupationCompletion

/-- `kform_integrable` fails without `a < 1` (at `a = 1`, `F = F' = 1`). -/
theorem drop_a_lt_one_refuted :
    ¬ ∀ a : ℝ, 0 ≤ a → ∀ F F' : ℝ → ℝ, MemLp F 2 timeMeasure → MemLp F' 2 timeMeasure →
      Integrable (fun q : ℝ × ℝ => kern a (q.1 - q.2) * ⟪F q.1, F' q.2⟫)
        (timeMeasure.prod timeMeasure) := by
  intro hall
  have h0 := hall 1 zero_le_one (fun _ => 1) (fun _ => 1) (memLp_const 1) (memLp_const 1)
  have h : Integrable (fun q : ℝ × ℝ => kern 1 (q.1 - q.2)) (timeMeasure.prod timeMeasure) :=
    h0.congr (ae_of_all _ fun q => by simp)
  have hs := h.prod_right_ae
  have hne : (timeMeasure : Measure ℝ) ≠ 0 := by
    intro h0
    have := congrArg (fun m : Measure ℝ => m (Ioo (0 : ℝ) 1)) h0
    simp at this
  have : (ae (timeMeasure : Measure ℝ)).NeBot := ae_neBot.2 hne
  obtain ⟨s, hsi, hsm⟩ := (hs.and (ae_restrict_mem measurableSet_Ioo)).exists
  have h1 : IntegrableOn (fun t => kern 1 (s - t)) (Ioo s 1) := by
    have h0 : IntegrableOn (fun t => kern 1 (s - t)) (Ioo 0 1) := hsi
    exact h0.mono_set fun t ht => ⟨hsm.1.trans ht.1, ht.2⟩
  have h2 : IntegrableOn (fun t => (t - s)⁻¹) (Ioo s 1) := by
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioo
    have hts : 0 < t - s := sub_pos.2 ht.1
    simp only [kern, Real.rpow_neg_one]
    rw [abs_sub_comm, abs_of_pos hts]
  have h3 : IntervalIntegrable (fun t => (t - s)⁻¹) volume s 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hsm.2.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact h2
  rcases intervalIntegrable_sub_inv_iff.1 h3 with h4 | h4
  · exact absurd h4 hsm.2.ne
  · exact h4 (left_mem_uIcc)

/-- The package theorem at `a = 1/2`, `F = F' = 1`. -/
theorem drop_a_lt_one_contrast :
    Integrable (fun q : ℝ × ℝ => kern (1 / 2) (q.1 - q.2) * ⟪(1 : ℝ), (1 : ℝ)⟫)
      (timeMeasure.prod timeMeasure) :=
  kform_integrable (F := fun _ : ℝ => (1 : ℝ)) (F' := fun _ : ℝ => (1 : ℝ)) (by norm_num)
    (by norm_num) (memLp_const 1) (memLp_const 1)

end Refutations.OccupationCompletion
