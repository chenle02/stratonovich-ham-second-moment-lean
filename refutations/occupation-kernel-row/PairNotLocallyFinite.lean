/-
Refutation for the local-finiteness hypothesis of `L:spatial-physical-pair`
(`notes/integrated_spatial_occupation.tex`, lines 12-33 at a284420; the proof,
line 25, uses "local finiteness of `Γ`"), package theorem
`StratonovichHAMSecondMoment.OccupationKernelRow.spatial_physical_pair` and
package definition `pairMeasure`.

Wrong variant: `ν(dx,dy) = dx Γ(dy)` is sigma-finite for every measure `Γ`
(local finiteness dropped).  Witness on `ℝ^1`: `Γ = ∞ · δ_0`.  For a measurable
`S`, `ν(S) = ∞ · Leb{x : (x,0) ∈ S}`, so every set of finite `ν`-measure has a
Lebesgue-null slice at `y = 0`; countably many of them cannot cover
`ℝ × {0}`.  `pair_contrast` applies the package theorem to the locally finite
`δ_0`.  No junk value is used.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationKernelRow

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace Refutations.OccupationKernelRow

open StratonovichHAMSecondMoment.OccupationKernelRow StratonovichHAMSecondMoment.HomogHypothesis

/-- The witness `Γ = ∞ · δ_0` on `ℝ^1`. -/
noncomputable abbrev infDirac : Measure (Rd 1) := (⊤ : ℝ≥0∞) • Measure.dirac 0

/-- A measurable set of finite `ν`-measure has a Lebesgue-null slice at `y = 0`. -/
theorem slice_null_of_finite (S : Set (Rd 1 × Rd 1)) (hS : MeasurableSet S)
    (hfin : pairMeasure infDirac S < ⊤) : volume {x : Rd 1 | (x, 0) ∈ S} = 0 := by
  have hT : MeasurableSet {x : Rd 1 | (x, 0) ∈ S} := measurable_prodMk_right hS
  have hval : pairMeasure infDirac S = ⊤ * volume {x : Rd 1 | (x, 0) ∈ S} := by
    rw [pairMeasure, Measure.prod_apply hS]
    have hfun : (fun x : Rd 1 => infDirac (Prod.mk x ⁻¹' S)) =
        {x : Rd 1 | (x, 0) ∈ S}.indicator (fun _ => ⊤) := by
      funext x
      rw [infDirac, Measure.smul_apply, Measure.dirac_apply' _ (measurable_prodMk_left hS)]
      by_cases hx : (x, (0 : Rd 1)) ∈ S
      · simp [hx]
      · simp [hx]
    rw [hfun, lintegral_indicator_const hT]
  rw [hval] at hfin
  by_contra h
  rw [ENNReal.top_mul h] at hfin
  exact lt_irrefl _ hfin

/-- Refuted variant: "`ν` is sigma-finite for every `Γ`". -/
theorem pair_sigmaFinite_false : ¬ ∀ Γ : Measure (Rd 1), SigmaFinite (pairMeasure Γ) := by
  intro h
  have hσ := h infDirac
  have hnull : ∀ n, volume {x : Rd 1 | (x, 0) ∈ spanningSets (pairMeasure infDirac) n} = 0 :=
    fun n => slice_null_of_finite _ (measurableSet_spanningSets _ n)
      (measure_spanningSets_lt_top _ n)
  have hcover : (univ : Set (Rd 1)) =
      ⋃ n, {x : Rd 1 | (x, 0) ∈ spanningSets (pairMeasure infDirac) n} := by
    ext x
    have : (x, (0 : Rd 1)) ∈ ⋃ n, spanningSets (pairMeasure infDirac) n := by
      rw [iUnion_spanningSets]; trivial
    rw [mem_iUnion] at this
    simpa only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff] using this
  have h0 : volume (univ : Set (Rd 1)) = 0 := by
    rw [hcover]
    exact measure_iUnion_null hnull
  exact (NeZero.ne (volume : Measure (Rd 1))) (Measure.measure_univ_eq_zero.1 h0)

/-- Contrast: for the locally finite `Γ = δ_0` the package theorem gives sigma-finiteness. -/
theorem pair_contrast : SigmaFinite (pairMeasure (Measure.dirac (0 : Rd 1))) :=
  (spatial_physical_pair (Measure.dirac (0 : Rd 1))).1

end Refutations.OccupationKernelRow
