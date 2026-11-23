import StratonovichHAMSecondMoment.FockColumnBound

/-!
Refutation for the orthonormality hypothesis of
`StratonovichHAMSecondMoment.FockColumnBound.sum_conv_le` (Bessel's inequality for the modes:
`∑_i |⟪ψ_i, k⟫|² ≤ ‖k‖²`, the step replacing the Gaussian isometry of main TeX lines 3437-3445
at edf7085f).

Wrong variant: unit vectors without orthogonality.  Counterexample: in `ℂ`, two copies of the
unit vector `1` and `k = 1`: the sum is `2 > 1 = ‖k‖²`.  No junk-value reliance.
`bessel_contrast` is the package lemma (an orthonormal family of modes in `L²(ν)`).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockColumnBound

open MeasureTheory
open StratonovichHAMSecondMoment.FockColumnBound
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- Bessel's inequality fails for repeated unit vectors. -/
theorem bessel_unit_only_refuted :
    ¬ ∀ (v : Fin 2 → ℂ) (k : ℂ), (∀ i, ‖v i‖ = 1) →
      ∑ i, ‖inner ℂ (v i) k‖ ^ 2 ≤ ‖k‖ ^ 2 := by
  intro h
  have := h (fun _ => 1) 1 (fun _ => by simp)
  norm_num at this

/-- Contrast: the package Bessel inequality for an orthonormal family of modes. -/
theorem bessel_contrast {d m : ℕ} {ν : Measure (Rd d)} (ψ : Fin m → Lp ℂ 2 ν)
    (hψ : Orthonormal ℂ ψ) (f : Lp ℂ 2 (volume : Measure (Rd d))) (η : Rd d) :
    ∑ i, ‖conv ν (ψ i) f η‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν :=
  sum_conv_le ψ hψ f η

end Refutations.FockColumnBound
