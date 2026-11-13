/-
Refutation for the constant `4` of the two-component Cauchy-Schwarz step in the proof
of `P:wave-two-variances` (`notes/integrated_wave_variance.tex` at a284420, lines
420-428: `∑_j ‖g_j‖² ≤ 2 ∑_{i,j} |V_i|² ‖𝒦_ij‖² ≤ 4 A_T h^{2-a} Φ_h ∑_i |V_i|²`), package
theorem `StratonovichHAMSecondMoment.WaveTwoVariances.sum_norm_sq_le`.

Wrong variant: the constant `4` replaced by `3`. With `H = ℂ`, every `k_ij = 1`,
`c = (1, 1)`, `M = 1`: the left side is `|2|² + |2|² = 8 > 6 = 3 · 1 · 2`. So the
constant `4` is sharp for this step. No junk value is involved.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveTwoVariances

set_option autoImplicit false

open StratonovichHAMSecondMoment.WaveTwoVariances (sum_norm_sq_le)

namespace Refutations.WaveTwoVariances

/-- The two-component step fails with the constant `3` in place of `4`. -/
theorem constant_three_fails :
    ¬ ∀ (c : Fin 2 → ℂ) (k : Fin 2 → Fin 2 → ℂ) (M : ℝ), (∀ i j, ‖k i j‖ ^ 2 ≤ M) →
      ∑ j, ‖∑ i, c i • k i j‖ ^ 2 ≤ 3 * M * ∑ i, ‖c i‖ ^ 2 := by
  intro hwrong
  have := hwrong (fun _ => 1) (fun _ _ => 1) 1 (fun _ _ => by simp)
  simp only [Fin.sum_univ_two, smul_eq_mul, mul_one, norm_one, one_pow] at this
  norm_num at this

/-- The package theorem at the same point: `8 ≤ 4 · 1 · 2`. -/
theorem constant_four_contrast :
    ∑ j : Fin 2, ‖∑ i : Fin 2, (fun _ => (1 : ℂ)) i • (fun _ _ => (1 : ℂ)) i j‖ ^ 2 ≤
      4 * 1 * ∑ i : Fin 2, ‖(fun _ => (1 : ℂ)) i‖ ^ 2 :=
  sum_norm_sq_le (fun _ => (1 : ℂ)) (fun _ _ => (1 : ℂ)) 1 (fun _ _ => by simp)

end Refutations.WaveTwoVariances
