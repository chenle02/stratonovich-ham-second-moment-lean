import StratonovichHAMSecondMoment.FockColumnBound

/-!
Refutation for the reality hypotheses behind
`StratonovichHAMSecondMoment.FockColumnBound.mulOp_isSelfAdjoint` and
`modeOp_isSelfAdjoint` (multiplication by a real function, and by a real mode `e_i`, is
self-adjoint; main TeX line 2990 at 39f2597a: "each multiplication `M_{e_i}` is bounded and
selfadjoint").

Wrong variant: multiplication by a complex constant is self-adjoint.  Counterexample: on
`X = ℂ`, multiplication by `i`: `⟪i·1, 1⟫ = -i ≠ i = ⟪1, i·1⟫`.  No junk-value reliance.
`complex_multiplier_contrast` is the package lemma for the real band indicator.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockColumnBound

open StratonovichHAMSecondMoment.FockColumnBound

/-- A complex (non-real) multiplier is not self-adjoint. -/
theorem complex_multiplier_refuted :
    ¬ ∀ z : ℂ, IsSelfAdjoint (z • ContinuousLinearMap.id ℂ ℂ) := by
  intro h
  have h1 := (h Complex.I).isSymmetric 1 1
  simp only [ContinuousLinearMap.coe_coe, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, RCLike.inner_apply', map_one,
    one_mul, Complex.conj_I] at h1
  have h2 := congrArg Complex.im h1
  simp at h2
  norm_num at h2

/-- Contrast: the package lemma for the real band indicator `1_{|η| ≤ 1}` on `ℝ¹`. -/
theorem complex_multiplier_contrast : IsSelfAdjoint (bandProj (d := 1) 1) :=
  bandProj_isSelfAdjoint 1

end Refutations.FockColumnBound
