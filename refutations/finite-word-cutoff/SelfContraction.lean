/-
Refutation for the retention of the lowering terms in `L:finite-word-cutoff`
(main TeX lines 3070-3073 at edf7085f: "The lowering term has been retained: the
assertion includes creation followed by annihilation and all resulting
self-contractions"), package theorem
`StratonovichHAMSecondMoment.FiniteWordCutoff.finite_word_cutoff` and the insertion
`StratonovichHAMSecondMoment.FiniteWordCutoff.field`.

Wrong variant: the compressed word at an admissible cutoff is a pure Wick (creation
only) chaos, with zero vacuum coefficient.  Counterexample: one color with one mode,
`𝒳 = ℂ`, `K = F = id`, start `1 ⊗ 1`, the word `g g` at cutoff `N = 2 = r`: the
vacuum coefficient is the self-contraction `E[g²] = 1`.
`self_contraction_contrast` is the one-letter word, whose vacuum coefficient is `0`.
No junk-value reliance (`√0 = 0` is the true value).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FiniteWordCutoff

set_option autoImplicit false

namespace Refutations.FiniteWordCutoff.SelfContraction

open StratonovichHAMSecondMoment.FiniteWordCutoff StratonovichHAMSecondMoment.FixedSplit
open StratonovichHAMSecondMoment.HermiteFock
open StratonovichHAMSecondMoment.GaussianHermite (unitIdx)

/-- The single color of the example. -/
abbrev col1 : Fin 1 → Unit := fun _ => ()

/-- The insertion operators of the example (identities). -/
noncomputable abbrev K1 : Fin 1 → ℂ →L[ℂ] ℂ := fun _ => ContinuousLinearMap.id ℂ ℂ

/-- The frame operators of the example (identities). -/
noncomputable abbrev F1 : Unit → ℂ →L[ℂ] ℂ := fun _ => ContinuousLinearMap.id ℂ ℂ

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

theorem raw2_zero :
    raw (field col1 K1) (fun b v l => F1 b (v l)) (vac 1) [((), ()), ((), ())] (ix 0) = 1 := by
  change field col1 K1 () (raw (field col1 K1) (fun b v l => F1 b (v l)) (vac 1)
    [((), ())]) (ix 0) = _
  rw [field_ix, raw1, raw1]
  simp

/-- The compressed word at the admissible cutoff `N = 2` keeps the self-contraction:
its vacuum coefficient is not zero. -/
theorem self_contraction_refuted :
    ¬ (cut (truncN col1 (fun _ => 2)) (field col1 K1) (fun b v l => F1 b (v l)) (vac 1)
        [((), ()), ((), ())] (ix 0) = 0) := by
  rw [finite_word_cutoff col1 K1 F1 1 (fun _ => 2) _ (fun i => by simp [counts, bump]),
    raw2_zero]
  exact one_ne_zero

/-- The one-letter word has zero vacuum coefficient (odd degree). -/
theorem self_contraction_contrast :
    cut (truncN col1 (fun _ => 2)) (field col1 K1) (fun b v l => F1 b (v l)) (vac 1)
      [((), ())] (ix 0) = 0 := by
  rw [finite_word_cutoff col1 K1 F1 1 (fun _ => 2) _ (fun i => by simp [counts, bump]),
    raw1]
  simp

end Refutations.FiniteWordCutoff.SelfContraction
