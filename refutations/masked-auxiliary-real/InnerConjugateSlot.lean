/-
Refutation for the inner product of the complexification in the real-`H`
clause of `P:masked-auxiliary-norm` (`notes/integrated_covariance_foundation.tex`,
line 117 at edf7085f), package definition
`StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.cxInner`
(conjugate linear in the first slot, Mathlib's convention, which the
`InnerProductSpace ℂ (Cx H)` instance certifies).

Wrong variant: the inner product of `Cx H` is complex linear in the first
slot, `⟪c x, y⟫ = c ⟪x, y⟫`.  Counterexample: `H = ℝ`, `c = i`, `x = y = ι 1`:
`⟪ι 1, ι 1⟫ = 1`, and `⟪i ι 1, ι 1⟫ = conj(i) = -i ≠ i`.
`inner_conjugate_slot_contrast` computes both values from the package.  No
junk value is involved.

Class (b): control of the Lean route (sign convention of the constructed
inner product; the norm, which is what the TeX's inequality uses, does not
depend on it).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedAuxiliaryReal

set_option autoImplicit false

open StratonovichHAMSecondMoment.MaskedAuxiliaryReal

namespace Refutations.MaskedAuxiliaryReal

/-- Contrast: `⟪ι 1, ι 1⟫ = 1` and `⟪i ι 1, ι 1⟫ = -i` in `Cx ℝ`. -/
theorem inner_conjugate_slot_contrast :
    inner ℂ (Cx.ofRealCLM (1 : ℝ)) (Cx.ofRealCLM (1 : ℝ)) = 1 ∧
      inner ℂ (Complex.I • Cx.ofRealCLM (1 : ℝ)) (Cx.ofRealCLM (1 : ℝ)) = -Complex.I := by
  constructor
  · rw [Cx.inner_eq]; apply Complex.ext <;> simp [Cx.cxInner]
  · rw [Cx.inner_eq]; apply Complex.ext <;> simp [Cx.cxInner]

/-- The inner product of `Cx H` is not linear in its first slot. -/
theorem inner_conjugate_slot_refuted :
    ¬ ∀ (c : ℂ) (x y : Cx ℝ), inner ℂ (c • x) y = c * inner ℂ x y := by
  intro h
  have h1 := h Complex.I (Cx.ofRealCLM 1) (Cx.ofRealCLM 1)
  rw [inner_conjugate_slot_contrast.1, inner_conjugate_slot_contrast.2, mul_one] at h1
  have h2 := congrArg Complex.im h1
  simp at h2
  norm_num at h2

end Refutations.MaskedAuxiliaryReal
