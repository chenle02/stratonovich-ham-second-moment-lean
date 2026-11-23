/-
Refutation for the vacuum insertion on coefficients `E:split-fresh-insertion`
(main TeX lines 3861-3898 at edf7085f), package theorem
`StratonovichHAMSecondMoment.FixedSplit.coef_insertion`.

Wrong variant: the insertion bound without the vacuum hypothesis (an
occupied color, "No occupied-color annihilation is estimated by a vacuum
bound", line 3897-3898): `∑_k ‖(g w)_k‖² ≤ ∑_l ‖w_l‖²` for every `w`.
Counterexample: one mode of one color, cutoff `N = 2`, `X = ℂ`, `w` the first
Hermite degree `e₁` with coefficient `1`.  Then `(g w)_0 = 1` (annihilation)
and `(g w)_{2e₁} = √2` (creation), so the left side is at least `3` while the
right side is `1`.  No junk-value reliance (finite sums of explicit values).
`occupied_insertion_contrast` is the package lemma for the vacuum vector.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FixedSplit

set_option autoImplicit false

namespace Refutations.FixedSplit

open StratonovichHAMSecondMoment.FixedSplit StratonovichHAMSecondMoment.HermiteFock Finset
open StratonovichHAMSecondMoment.GaussianHermite (unitIdx)

/-- One mode, one color. -/
def col1 : Fin 1 → Unit := fun _ => ()

/-- Cutoff `N = 2`. -/
def N2 : Unit → ℕ := fun _ => 2

/-- The multi-index `2e₁`. -/
def two1 : Fin 1 → ℕ := Pi.single 0 2

/-- The first-degree vector `w = e₁`. -/
noncomputable def wOcc : Fin 1 → (Fin 1 → ℕ) → ℂ := fun _ l => if l = unitIdx 0 then 1 else 0

/-- The vacuum vector. -/
noncomputable def wVac : Fin 1 → (Fin 1 → ℕ) → ℂ := fun _ l => if l = 0 then 1 else 0

theorem colorDeg_col1 (k : Fin 1 → ℕ) : colorDeg col1 k () = k 0 := by
  simp [colorDeg, col1]

theorem mem_cut1 (k : Fin 1 → ℕ) : k ∈ cutIdx col1 N2 ↔ k 0 ≤ 2 := by
  rw [mem_cutIdx]
  constructor
  · intro h; simpa [colorDeg_col1, N2] using h ()
  · intro h u; cases u; rw [colorDeg_col1]; exact h

theorem filter_col1 : (univ.filter fun j : Fin 1 => col1 j = ()) = univ := by
  ext j; simp [col1]

theorem two1_sub : two1 - unitIdx 0 = unitIdx 0 := by
  funext i; fin_cases i; simp [two1, unitIdx]

theorem gmul_zero_occ : gmul 0 (wOcc 0) 0 = 1 := by
  simp [gmul, cre, ann, wOcc]

theorem gmul_two_occ : gmul 0 (wOcc 0) two1 = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h3 : two1 + unitIdx 0 ≠ unitIdx 0 := by
    intro h; have := congrFun h 0; simp [two1, unitIdx] at this
  simp only [gmul, cre, ann, wOcc, two1_sub, h3, ite_true, ite_false, smul_zero, add_zero]
  simp [two1]

/-- The vacuum bound fails on an occupied color. -/
theorem occupied_insertion_refuted :
    ¬ (∀ w : Fin 1 → (Fin 1 → ℕ) → ℂ,
        ∑ k ∈ cutIdx col1 N2, ‖∑ j ∈ univ.filter (fun j => col1 j = ()), gmul j (w j) k‖ ^ 2 ≤
          ∑ j ∈ univ.filter (fun j => col1 j = ()), ∑ l ∈ cutIdx col1 N2, ‖w j l‖ ^ 2) := by
  intro hall
  have h := hall wOcc
  rw [filter_col1] at h
  simp only [Fin.sum_univ_one] at h
  have h0 : (0 : Fin 1 → ℕ) ∈ cutIdx col1 N2 := (mem_cut1 _).2 (by simp)
  have h2 : two1 ∈ cutIdx col1 N2 := (mem_cut1 _).2 (by simp [two1])
  have he : unitIdx (0 : Fin 1) ∈ cutIdx col1 N2 := (mem_cut1 _).2 (by simp [unitIdx])
  have hne : (0 : Fin 1 → ℕ) ≠ two1 := by
    intro h; have := congrFun h 0; simp [two1] at this
  have hsub : ({0, two1} : Finset (Fin 1 → ℕ)) ⊆ cutIdx col1 N2 := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hlow := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => ‖gmul 0 (wOcc 0) k‖ ^ 2) hsub
    fun _ _ _ => sq_nonneg _
  rw [Finset.sum_pair hne, gmul_zero_occ, gmul_two_occ] at hlow
  have hr : ∑ l ∈ cutIdx col1 N2, ‖wOcc 0 l‖ ^ 2 = 1 := by
    simp only [wOcc, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_one, one_pow, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [Finset.sum_ite_eq' _ _ (fun _ => (1 : ℝ))]
    simp [he]
  rw [hr] at h
  have hs : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
  rw [hs] at hlow
  simp only [norm_one, one_pow] at hlow
  linarith

/-- Contrast: the package lemma for the vacuum vector of the occupied
color's complement (color degree zero). -/
theorem occupied_insertion_contrast :
    ∑ k ∈ cutIdx col1 N2, ‖∑ j ∈ univ.filter (fun j => col1 j = ()), gmul j (wVac j) k‖ ^ 2 ≤
      ∑ j ∈ univ.filter (fun j => col1 j = ()), ∑ l ∈ cutIdx col1 N2, ‖wVac j l‖ ^ 2 :=
  coef_insertion col1 N2 () wVac fun j _ l hl => by
    have : l = 0 := by by_contra h; exact hl (by simp [wVac, h])
    simp [this, colorDeg]

end Refutations.FixedSplit
