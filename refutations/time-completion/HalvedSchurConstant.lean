/-
Refutation for `E:masked-time-schur` (`notes/integrated_covariance_foundation.tex`
lines 150-152 at a284420), package theorem
`StratonovichHAMSecondMoment.TimeCompletion.emb_norm_sq_le`.

Wrong variant: the Schur constant `2T^{1-a}/(1-a)` halved to `T^{1-a}/(1-a)`, i.e.
`‖f‖_a² ≤ (T^{1-a}/(1-a)) ∫_0^T |f|²` for every `f ∈ L²(0,T)`.
Counterexample: `a = 1/2`, `T = 1`, `f = 1`: `‖1‖_a² = 2T^{2-a}/((1-a)(2-a)) = 8/3`
(package calibration `timeForm_one`), while the halved bound is `2`.
`halved_schur_contrast` is the package bound at the same point: `8/3 ≤ 4`.
No junk-value reliance (`f = 1` is in `L²(0,1)`; the integrals are of integrable
functions).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TimeCompletion

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment TimeCompletion

namespace Refutations.TimeCompletion

/-- The parameters `a = 1/2`, `T = 1`. -/
noncomputable abbrev pHalf' : TimeParams := ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩

/-- The constant function `1` in `L²(0,1)`. -/
noncomputable def one' : L2fun pHalf'.T := ⟨fun _ => (1 : ℂ), memLp_const 1⟩

/-- `‖emb 1‖² = 8/3` at `a = 1/2`, `T = 1`. -/
theorem norm_sq_one : ‖emb pHalf' one'‖ ^ 2 = 8 / 3 := by
  rw [emb_norm_sq]
  change (StratonovichHAMSecondMoment.TimeSchur.timeForm (1 / 2) 1 (fun _ => (1 : ℂ))
    (fun _ => (1 : ℂ))).re = _
  rw [timeForm_one (by norm_num) (by norm_num), Complex.ofReal_re]
  norm_num

/-- `∫_0^1 |1|² = 1`. -/
theorem integral_one_sq : ∫ t in Icc (0 : ℝ) 1, ‖(one' : ℝ → ℂ) t‖ ^ 2 = 1 := by
  simp [one']

/-- The package Schur bound at the counterexample: `8/3 ≤ 2 · 1^{1/2}/(1/2) · 1 = 4`. -/
theorem halved_schur_contrast :
    ‖emb pHalf' one'‖ ^ 2 ≤ schurConst pHalf' * ∫ t in Icc (0 : ℝ) 1, ‖(one' : ℝ → ℂ) t‖ ^ 2 :=
  emb_norm_sq_le one'

/-- The halved Schur constant is false. -/
theorem halved_schur_refuted :
    ¬ (∀ f : L2fun pHalf'.T, ‖emb pHalf' f‖ ^ 2 ≤
        (1 : ℝ) ^ (1 - (1 / 2 : ℝ)) / (1 - 1 / 2) * ∫ t in Icc (0 : ℝ) 1, ‖(f : ℝ → ℂ) t‖ ^ 2) := by
  intro h
  have h1 := h one'
  rw [norm_sq_one, integral_one_sq, Real.one_rpow] at h1
  norm_num at h1

end Refutations.TimeCompletion
