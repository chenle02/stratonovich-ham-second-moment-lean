/-
Refutation for the Lipschitz bound of `λ_z²` in part (i) of
`L:spatial-static-controls` (`notes/integrated_spatial_occupation.tex` lines
62-63 at a284420: "Lipschitz with constant `‖U_z‖_∞`"), package theorem
`StratonovichHAMSecondMoment.SpatialStaticControls.lamSq_lip`.

Wrong variant: the constant `‖U‖_∞ / 2` instead of `‖U‖_∞`, i.e.
`|λ_U(c)² - λ_U(c')²| ≤ (M/2) |c - c'|` for every continuous `0 ≤ U ≤ M`.
Counterexample: `d = 1`, `U = 1`, `M = 1`, `c = 1`, `c' = 0`: `λ_U(c)² = c`
(`lamSq_const`), so the left side is `1 > 1/2`.  The constant `‖U‖_∞` is
attained for constant potentials.  `lipschitz_half_constant_contrast` applies
the package theorem at the same point.
No junk-value reliance (the Rayleigh sets are nonempty and bounded).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialStaticControls

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis SpatialStaticControls

namespace Refutations.SpatialStaticControls

/-- Halving the Lipschitz constant of `λ²` is false. -/
theorem lipschitz_half_constant_refuted :
    ¬ (∀ (U : Rd 1 → ℝ) (M : ℝ), Continuous U → (∀ x, 0 ≤ U x) → (∀ x, U x ≤ M) →
        ∀ c c' : ℝ, |lamSq U c - lamSq U c'| ≤ M / 2 * |c - c'|) := by
  intro h
  have := h (fun _ => 1) 1 continuous_const (fun _ => zero_le_one) (fun _ => le_rfl) 1 0
  rw [lamSq_const, lamSq_const] at this
  norm_num at this

/-- Contrast: the package bound with constant `M` at the same point. -/
theorem lipschitz_half_constant_contrast :
    |lamSq (fun _ : Rd 1 => (1 : ℝ)) 1 - lamSq (fun _ : Rd 1 => (1 : ℝ)) 0| ≤ 1 * |1 - 0| :=
  lamSq_lip continuous_const (fun _ => zero_le_one) (fun _ => le_rfl) 1 0

end Refutations.SpatialStaticControls
