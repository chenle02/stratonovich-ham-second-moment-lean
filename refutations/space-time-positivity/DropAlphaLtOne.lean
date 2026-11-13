/-
Refutation for the integrability of the space-time kernel, package theorems
`StratonovichHAMSecondMoment.SpaceTimePositivity.kern_integrable` and
`stIntegrand_integrable` (`|s-t|^{-a}` integrable on `(0,1)²` for `a < 1`; auxiliary to the
Lean route of step (c) of the S1Bdd discharge; the TeX's `a = α₀ < 1`,
`integrated_occupation_ceiling.tex` lines 4-6 at a284420).

Wrong variant: the hypothesis `a < 1` dropped, i.e. `|s-t|^{-1}` integrable on `(0,1)²`.
Counterexample: `a = 1`.  If it were integrable, then for a.e. `s ∈ (0,1)` the section
`t ↦ |s-t|^{-1}` would be integrable on `(0,1)`, hence `t ↦ (t-s)⁻¹` on `(s,1)`, which
`intervalIntegrable_sub_inv_iff` excludes.  `drop_alpha_lt_one_contrast` is the package
theorem at `a = 1/2`.  No junk-value reliance (the diagonal value `0^{-1} = 0` is on a null
set and plays no role).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpaceTimePositivity

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment SpaceTimePositivity TimeSchur

namespace Refutations.SpaceTimePositivity

/-- Integrability of `|s-t|^{-a}` on `(0,1)²` fails at `a = 1`. -/
theorem drop_alpha_lt_one_refuted :
    ¬ Integrable (fun p : ℝ × ℝ => kern 1 (p.1 - p.2)) (timeMeasure.prod timeMeasure) := by
  intro h
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

/-- The package bound at `a = 1/2`. -/
theorem drop_alpha_lt_one_contrast :
    Integrable (fun p : ℝ × ℝ => kern (1 / 2) (p.1 - p.2)) (timeMeasure.prod timeMeasure) :=
  kern_integrable (by norm_num)

end Refutations.SpaceTimePositivity
