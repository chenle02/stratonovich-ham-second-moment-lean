import StratonovichHAMSecondMoment.FockForm

/-!
Refutation for `StratonovichHAMSecondMoment.FockForm.truncC_eq` (hypothesis `hP` of
`HermiteWord.cut_eq_raw`: the cutoff fixes vectors whose color degrees are within the cutoffs;
`L:finite-word-cutoff`, main TeX lines 2531-2570 at a284420).

Wrong variant: the truncation fixes every degree-supported vector, without `d ≤ N`.
Counterexample: one color, cutoff `N = 0`, degree `d = 1`, `v_k = 1` for `k_0 ≤ 1`: the
truncation kills the coefficient at `k_0 = 1`.  No junk-value reliance.  `trunc_contrast` is
the package lemma with `N = d = 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockForm

open StratonovichHAMSecondMoment.FockForm

/-- Auxiliary: the test vector, supported in color degree `≤ 1`. -/
def testVec : (Fin 1 → ℕ) → ℂ := fun k => if k 0 ≤ 1 then 1 else 0

/-- Auxiliary: `testVec` has color degree at most `1`. -/
theorem testVec_good : GoodDeg (fun _ => 1) testVec := by
  rintro k ⟨c, hc⟩
  have : c = 0 := Subsingleton.elim _ _
  subst this
  simp [testVec]; omega

/-- The truncation does not fix vectors beyond the cutoff. -/
theorem trunc_without_cutoff_refuted :
    ¬ (∀ (Nc d : Fin 1 → ℕ) (v : (Fin 1 → ℕ) → ℂ), GoodDeg d v → truncC Nc v = v) := by
  intro h
  have := congrFun (h (fun _ => 0) (fun _ => 1) testVec testVec_good) (fun _ => 1)
  simp [truncC, testVec] at this

/-- Contrast: the package lemma with cutoff `N = 1 = d`. -/
theorem trunc_contrast : truncC (fun _ => 1) testVec = testVec :=
  truncC_eq _ (fun _ => 1) testVec (fun _ => le_rfl) testVec_good

end Refutations.FockForm
