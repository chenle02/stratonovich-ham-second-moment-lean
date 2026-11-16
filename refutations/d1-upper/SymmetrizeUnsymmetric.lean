/-
Control for the symmetry hypothesis of the Lean form of `E:d1-time-symmetry`
(main TeX lines 5500-5507 at 39f2597a; the TeX stresses that "this symmetry is
applied to the *sum* of pairings ..., not to an individual temporally weighted
diagram").  Package theorem
`StratonovichHAMSecondMoment.D1Upper.card_mul_lintegral_twoSimplex_le`.

Wrong variant: the inequality `m! n! ∫_{simplex} F ≤ ∫_{cube} F` for every
measurable `F ≥ 0`, without the permutation invariance.  Counterexample:
`m = 2`, `n = 0`, `t = 1`, `F` the indicator of the simplex `{0 < s_0 < s_1 < 1}`
itself: `2 vol(S) ≤ vol(S)` fails since `0 < vol(S) < ∞`.
`symmetrizeUnsymmetric_contrast` is the package inequality for invariant `F`.
Class (b): Lean-route-only control (the hypothesis of a Lean auxiliary
formulation of the TeX's step).  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.D1Upper

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment DiagramModel D1Upper
open scoped ENNReal Nat

namespace Refutations.D1Upper.SymmetrizeUnsymmetric

/-- A box inside the simplex `{0 < s_0 < s_1 < 1}`. -/
theorem box_subset : (Set.univ.pi ![Ioo (1 / 10 : ℝ) (2 / 10), Ioo (3 / 10 : ℝ) (4 / 10)]) ⊆
    twoSimplex 2 0 1 := by
  intro s hs i
  have h0 := hs 0 (mem_univ _)
  have h1 := hs 1 (mem_univ _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mem_Ioo] at h0 h1
  fin_cases i
  · simp [predVal, pred]; constructor <;> linarith
  · simp [predVal, pred]; constructor <;> linarith

/-- The simplex has positive, finite volume. -/
theorem vol_pos_finite : 0 < volume (twoSimplex 2 0 1) ∧ volume (twoSimplex 2 0 1) < ⊤ := by
  constructor
  · refine lt_of_lt_of_le ?_ (measure_mono box_subset)
    rw [volume_pi_pi]
    simp [Fin.prod_univ_two, Real.volume_Ioo]
    norm_num
  · refine lt_of_le_of_lt (measure_mono (t := Set.univ.pi fun _ : Fin (2 + 0) => Icc 0 1)
      fun s hs i _ => ⟨(pos_of_mem_twoSimplex hs i).le, (hs i).2.le⟩) ?_
    rw [volume_pi_pi]
    simp

/-- The package: the inequality for a permutation-invariant `F`. -/
theorem symmetrizeUnsymmetric_contrast : ∀ F : (Fin (2 + 0) → ℝ) → ℝ≥0∞, Measurable F →
    (∀ (σ : Equiv.Perm (Fin (2 + 0))) (s : Fin (2 + 0) → ℝ), F (s ∘ σ) = F s) →
    ((2 ! * 0 ! : ℕ) : ℝ≥0∞) * ∫⁻ s in twoSimplex 2 0 1, F s ≤
      ∫⁻ s in Set.univ.pi (fun _ : Fin (2 + 0) => Icc 0 1), F s :=
  fun _ hF hsym => card_mul_lintegral_twoSimplex_le 1 hF hsym

/-- Without the invariance the inequality is false. -/
theorem symmetrizeUnsymmetric_refuted : ¬ (∀ F : (Fin (2 + 0) → ℝ) → ℝ≥0∞, Measurable F →
    ((2 ! * 0 ! : ℕ) : ℝ≥0∞) * ∫⁻ s in twoSimplex 2 0 1, F s ≤
      ∫⁻ s in Set.univ.pi (fun _ : Fin (2 + 0) => Icc 0 1), F s) := by
  intro H
  have hS := measurableSet_twoSimplex 2 0 1
  have h := H ((twoSimplex 2 0 1).indicator 1) (measurable_one.indicator hS)
  have hl : ∫⁻ s in twoSimplex 2 0 1, (twoSimplex 2 0 1).indicator 1 s =
      volume (twoSimplex 2 0 1) := by
    rw [setLIntegral_congr_fun hS fun s hs => Set.indicator_of_mem hs _]
    simp
  have hr : ∫⁻ s in Set.univ.pi (fun _ : Fin (2 + 0) => Icc 0 1),
      (twoSimplex 2 0 1).indicator 1 s ≤ volume (twoSimplex 2 0 1) :=
    (setLIntegral_le_lintegral _ _).trans (lintegral_indicator_one hS).le
  rw [hl] at h
  obtain ⟨hpos, hfin⟩ := vol_pos_finite
  have h2 := h.trans hr
  norm_num at h2
  have h4 := ENNReal.toReal_mono hfin.ne h2
  rw [ENNReal.toReal_mul] at h4
  have h5 := ENNReal.toReal_pos hpos.ne' hfin.ne
  norm_num at h4
  linarith

end Refutations.D1Upper.SymmetrizeUnsymmetric
