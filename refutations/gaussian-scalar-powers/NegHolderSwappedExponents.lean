import StratonovichHAMSecondMoment.GaussianScalarPowers

/-!
Refutation for `StratonovichHAMSecondMoment.GaussianScalarPowers.finite_holder`
(manuscript `L:gaussian-scalar-powers`, part (3)): the outer exponents `1/m` and
`(m-1)/m` cannot be swapped.

The wrong variant is the package statement (same binders and hypotheses, the
index type quantified over `Type`) with the outer exponents exchanged.
Counterexample: `ι = Fin 1`, `s = univ`, `m = 3`, `a = 1`, `b = 4`:
LHS `= 4`, swapped RHS `= 1 * (4^(3/2))^(1/3) = 2`.
This is strictly more faithful than the earlier Mathlib-only version, which
fixed `ι = Fin 1`, `s = univ` in the statement itself.
The contrast theorem applies the package theorem at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.GaussianScalarPowers

/-- `finite_holder` with swapped outer exponents is false. -/
theorem finite_holder_swapped_exponents :
    ¬ (∀ (ι : Type) (s : Finset ι) (a b : ι → ℝ) (m : ℝ), 1 < m →
      (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, 0 ≤ b i) →
      ∑ i ∈ s, a i * b i ≤
        (∑ i ∈ s, a i ^ m) ^ ((m - 1) / m) *
          (∑ i ∈ s, b i ^ (m / (m - 1))) ^ (1 / m)) := by
  intro h
  have := h (Fin 1) Finset.univ (fun _ => 1) (fun _ => 4) 3 (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
  simp only [Finset.univ_unique, Finset.sum_singleton, Real.one_rpow, one_mul] at this
  rw [← Real.rpow_mul (by norm_num)] at this
  have h4 : (4 : ℝ) ^ ((3 : ℝ) / (3 - 1) * (1 / 3)) = 2 := by
    rw [show (3 : ℝ) / (3 - 1) * (1 / 3) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at this
  norm_num at this

/-- Contrast: at the counterexample (`ι = Fin 1`, `m = 3`, `a = 1`, `b = 4`)
the package statement (correct exponents) holds. -/
theorem finite_holder_swapped_exponents_contrast :
    ∑ i ∈ (Finset.univ : Finset (Fin 1)), (fun _ => (1 : ℝ)) i * (fun _ => (4 : ℝ)) i ≤
      (∑ i ∈ (Finset.univ : Finset (Fin 1)), (fun _ => (1 : ℝ)) i ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) *
        (∑ i ∈ (Finset.univ : Finset (Fin 1)),
          (fun _ => (4 : ℝ)) i ^ ((3 : ℝ) / (3 - 1))) ^ (((3 : ℝ) - 1) / 3) :=
  StratonovichHAMSecondMoment.GaussianScalarPowers.finite_holder Finset.univ
    (fun _ => 1) (fun _ => 4) 3 (by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num)

end Refutations.GaussianScalarPowers
