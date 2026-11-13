/-
Refutation for the Lipschitz claim of part (i) of `L:spatial-static-controls`
(`notes/integrated_spatial_occupation.tex` lines 47-48 at a284420: "`λ_z` is
Lipschitz on every compact positive `c` interval"), package theorem
`StratonovichHAMSecondMoment.SpatialStaticControls.lam_lipschitzOn`.

Wrong variant: dropping positivity of the interval, i.e. `λ` Lipschitz on
`[0, 1]`.  Counterexample: `d = 1`, `U = 1`: `λ_U(c) = √c` (`lamSq_const`),
and `√c ≤ K c` fails at `c = 1/(K+1)²`.  `lipschitz_at_zero_contrast` applies
the package theorem on `[1, 2]`, where `λ_U(1)² = 1 > 0`.
No junk-value reliance (`c ≥ 0`, so `√` is applied to a nonnegative number).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialStaticControls

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment HomogHypothesis SpatialStaticControls

namespace Refutations.SpatialStaticControls

/-- `λ` is not Lipschitz on an interval reaching `0`. -/
theorem lipschitz_at_zero_refuted :
    ¬ ∃ K : NNReal, LipschitzOnWith K (lam (fun _ : Rd 1 => (1 : ℝ))) (Icc 0 1) := by
  rintro ⟨K, hK⟩
  set k : ℝ := (K : ℝ) with hkdef
  have hk : 0 ≤ k := K.2
  set c : ℝ := 1 / (k + 1) ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one (by positivity)]
    nlinarith
  have h := hK.dist_le_mul c ⟨hc0.le, hc1⟩ 0 ⟨le_rfl, zero_le_one⟩
  rw [lam_eq_sqrt, lam_eq_sqrt, lamSq_const, lamSq_const, Real.dist_eq, Real.dist_eq] at h
  have hs : Real.sqrt (c * 1) = 1 / (k + 1) := by
    rw [mul_one, hcdef, Real.sqrt_div' 1 (by positivity), Real.sqrt_one,
      Real.sqrt_sq (by positivity)]
  rw [hs, zero_mul, Real.sqrt_zero, sub_zero, sub_zero, abs_of_pos (by positivity),
    abs_of_pos hc0, hcdef] at h
  have : (k : ℝ) * (1 / (k + 1) ^ 2) < 1 / (k + 1) := by
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- Contrast: the package theorem on the positive interval `[1, 2]`. -/
theorem lipschitz_at_zero_contrast :
    ∃ K : NNReal, LipschitzOnWith K (lam (fun _ : Rd 1 => (1 : ℝ))) (Icc 1 2) :=
  lam_lipschitzOn continuous_const (fun _ => zero_le_one) (fun _ => le_rfl)
    (by rw [lamSq_const]; norm_num)

end Refutations.SpatialStaticControls
