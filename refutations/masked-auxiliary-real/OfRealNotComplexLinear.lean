/-
Refutation for the real embedding of the real-`H` clause of
`P:masked-auxiliary-norm` (`notes/integrated_covariance_foundation.tex`,
line 117 at 39f2597a), package definition
`StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.ofRealCLM`
(`ι v = v + 0i`, real linear and isometric, `norm_ofReal`).

Wrong variant: `ι` is complex linear, `ι(Re c · v) = c · ι v` (a real `H`
would then already carry the complex structure, and no complexification would
be needed).  Counterexample: `H = ℝ`, `c = i`, `v = 1`: the left side is
`ι 0 = 0`, the right side is `i · 1 = 0 + 1i ≠ 0`.
`of_real_not_complex_linear_contrast` is the isometry `‖ι 1‖ = 1` with the
value `Im(i · ι 1) = 1`.  No junk value is involved.

Class (b): control of the Lean route.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedAuxiliaryReal

set_option autoImplicit false

open StratonovichHAMSecondMoment.MaskedAuxiliaryReal

namespace Refutations.MaskedAuxiliaryReal

/-- Contrast: `‖ι 1‖ = 1` and `Im(i · ι 1) = 1` in `Cx ℝ`. -/
theorem of_real_not_complex_linear_contrast :
    ‖Cx.ofRealCLM (1 : ℝ)‖ = 1 ∧ (Complex.I • Cx.ofRealCLM (1 : ℝ)).im = 1 := by
  refine ⟨by rw [Cx.norm_ofReal, norm_one], ?_⟩
  simp

/-- `ι` is not complex linear. -/
theorem of_real_not_complex_linear_refuted :
    ¬ ∀ (c : ℂ) (v : ℝ), Cx.ofRealCLM (c.re • v) = c • Cx.ofRealCLM v := by
  intro h
  have h1 := congrArg Cx.im (h Complex.I 1)
  rw [of_real_not_complex_linear_contrast.2] at h1
  simp at h1

end Refutations.MaskedAuxiliaryReal
