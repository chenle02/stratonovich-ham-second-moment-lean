/-
Refutation for the second identity of `E:spatial-dilation`
(`notes/integrated_spatial_occupation.tex` line 192 at a284420), package theorem
`StratonovichHAMSecondMoment.SpatialSmoothRatio.gradEnergy_dilL2`
(`b(U_ℓ g) = ℓ² b(g)`).

Wrong variant: `b(U_ℓ g) = ℓ b(g)` (the chain-rule factor not squared).
Counterexample: `d = 1`, `ℓ = 2`, `g` a real unit test: the package identity
gives `4 b(g)`, the variant `2 b(g)`, and `b(g) > 0` (`gradEnergy_pos`).
`grad_dilation_contrast` is the package identity at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialSmoothRatio

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment HomogHypothesis SpatialFourierBound
  SpatialSmoothRatio

namespace Refutations.SpatialSmoothRatio

/-- `b(U_ℓ g) = ℓ b(g)` is false. -/
theorem grad_dilation_refuted :
    ¬ (∀ ℓ : ℝ, 0 < ℓ → ∀ g : Rd 1 → ℝ, IsUnitTest g →
        gradEnergy (WeakSobolev.dilL2 ℓ g) = ℓ * gradEnergy g) := by
  intro h
  obtain ⟨g, hg⟩ := exists_unitTest 1
  have h1 := h 2 two_pos g hg
  have h2 := gradEnergy_dilL2 two_pos (hg.1.differentiable (by simp))
  have hb := gradEnergy_pos one_pos hg
  rw [h2] at h1
  linarith

/-- The package identity at the same point: `b(U_2 g) = 4 b(g)`. -/
theorem grad_dilation_contrast {g : Rd 1 → ℝ} (hg : IsUnitTest g) :
    gradEnergy (WeakSobolev.dilL2 2 g) = 2 ^ 2 * gradEnergy g :=
  gradEnergy_dilL2 two_pos (hg.1.differentiable (by simp))

end Refutations.SpatialSmoothRatio
