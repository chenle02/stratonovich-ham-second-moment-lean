/-
Refutation for the count hypothesis `r_i ≤ N_i` of `L:finite-word-cutoff`
(main TeX lines 3036-3058 at 39f2597a, `E:finite-word-cutoff` 3048-3055), package
theorem `StratonovichHAMSecondMoment.FiniteWordCutoff.finite_word_cutoff`.

Wrong variant: the compressed word equals the uncompressed word at every cutoff.
Counterexample: one color with one mode (`m = 1`), `𝒳 = ℂ`, `K = F = id`, start
`1 ⊗ 1`, the word `g g` of two insertions, cutoff `N = 1 < 2 = r`.  The
uncompressed word `g² = √2 h_2 + h_0` has coefficient `√2` at degree 2; the
compressed word is projected to degree `≤ 1`, so its degree-2 coefficient is `0`.
`cutoff_below_counts_contrast` is the package theorem at `N = 2` on the same word,
with the same degree-2 coefficient `√2`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FiniteWordCutoff

set_option autoImplicit false

namespace Refutations.FiniteWordCutoff.BelowCounts

open StratonovichHAMSecondMoment.FiniteWordCutoff StratonovichHAMSecondMoment.FixedSplit
open StratonovichHAMSecondMoment.HermiteFock
open StratonovichHAMSecondMoment.GaussianHermite (unitIdx)

/-- The single color of the example. -/
abbrev col1 : Fin 1 → Unit := fun _ => ()

/-- The insertion and frame operators of the example (identities). -/
noncomputable abbrev K1 : Fin 1 → ℂ →L[ℂ] ℂ := fun _ => ContinuousLinearMap.id ℂ ℂ

/-- The frame operators of the example (identities). -/
noncomputable abbrev F1 : Unit → ℂ →L[ℂ] ℂ := fun _ => ContinuousLinearMap.id ℂ ℂ

/-- The word `g g`. -/
abbrev w2 : List (Unit × Unit) := [((), ()), ((), ())]

/-- The constant multi-index of degree `n`. -/
abbrev ix (n : ℕ) : Fin 1 → ℕ := fun _ => n

theorem ix_sub (n : ℕ) : ix n - unitIdx 0 = ix (n - 1) := by
  funext j; fin_cases j; simp [ix]

theorem ix_add (n : ℕ) : ix n + unitIdx 0 = ix (n + 1) := by
  funext j; fin_cases j; simp [ix]

theorem ix_eq_zero (n : ℕ) : ix n = 0 ↔ n = 0 := by
  constructor
  · intro h; have := congrFun h 0; simpa [ix] using this
  · rintro rfl; rfl

theorem field_ix (v : (Fin 1 → ℕ) → ℂ) (n : ℕ) :
    field col1 K1 () v (ix n) =
      (Real.sqrt n : ℂ) * v (ix (n - 1)) + (Real.sqrt (n + 1) : ℂ) * v (ix (n + 1)) := by
  simp [field, gmul, cre, ann, K1]
  rw [ix_sub, ix_add]

theorem raw1 (n : ℕ) :
    raw (field col1 K1) (fun b v l => F1 b (v l)) (vac 1) [((), ())] (ix n) =
      if n = 1 then 1 else 0 := by
  change field col1 K1 () (vac 1) (ix n) = _
  rw [field_ix]
  simp only [vac, ix_eq_zero]
  rcases n with _ | _ | n <;> simp

theorem raw2 (n : ℕ) :
    raw (field col1 K1) (fun b v l => F1 b (v l)) (vac 1) w2 (ix n) =
      (Real.sqrt n : ℂ) * (if n - 1 = 1 then 1 else 0) +
        (Real.sqrt (n + 1) : ℂ) * (if n + 1 = 1 then 1 else 0) := by
  change field col1 K1 () (raw (field col1 K1) (fun b v l => F1 b (v l)) (vac 1)
    [((), ())]) (ix n) = _
  rw [field_ix, raw1, raw1]

theorem raw2_two :
    raw (field col1 K1) (fun b v l => F1 b (v l)) (vac 1) w2 (ix 2) = (Real.sqrt 2 : ℂ) := by
  rw [raw2]; norm_num

theorem not_mem_cut (N : ℕ) (n : ℕ) (h : N < n) : ix n ∉ cutIdx col1 (fun _ => N) := by
  rw [mem_cutIdx]
  intro hk
  have := hk ()
  simp [colorDeg, ix] at this
  omega

/-- The compressed word at a cutoff below the counts is not the uncompressed word. -/
theorem cutoff_below_counts_refuted :
    ¬ (∀ N : ℕ, cut (truncN col1 (fun _ => N)) (field col1 K1) (fun b v l => F1 b (v l))
        (vac 1) w2 = raw (field col1 K1) (fun b v l => F1 b (v l)) (vac 1) w2) := by
  intro hall
  have h := congrFun (hall 1) (ix 2)
  rw [raw2_two] at h
  have h0 : cut (truncN col1 (fun _ => 1)) (field col1 K1) (fun b v l => F1 b (v l))
      (vac 1) w2 (ix 2) = 0 := by
    change F1 () (truncN col1 (fun _ => 1) _ (ix 2)) = 0
    simp [truncN, not_mem_cut 1 2 (by norm_num)]
  rw [h0] at h
  have : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  exact this h.symm

/-- The package theorem at `N = 2 = r` on the same word: the degree-2 coefficient of
the compressed word is `√2`. -/
theorem cutoff_below_counts_contrast :
    cut (truncN col1 (fun _ => 2)) (field col1 K1) (fun b v l => F1 b (v l))
        (vac 1) w2 (ix 2) = (Real.sqrt 2 : ℂ) := by
  rw [finite_word_cutoff col1 K1 F1 1 (fun _ => 2) w2 (fun i => by
    simp [counts, bump])]
  exact raw2_two

end Refutations.FiniteWordCutoff.BelowCounts
