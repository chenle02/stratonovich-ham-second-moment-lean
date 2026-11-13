/-
Refutation for `E:spatial-dilation` (`notes/integrated_spatial_occupation.tex`
lines 189-195 at a284420), package theorem
`StratonovichHAMSecondMoment.SpatialSmoothRatio.spatialEnergy_dilL2`
(`A_sp(U_ℓ g) = ℓ^α A_sp(g)` under `Γ(cA) = c^{d-α}Γ(A)`).

Wrong variant: the exponent `α + 1` instead of `α` (a miscount of the factors
`ℓ^{2d} ℓ^{-d} ℓ^{α-d}`), i.e. `A_sp(U_ℓ g) = ℓ^{α+1} A_sp(g)` for every
locally finite `Γ` with `Γ(cA) = c^{d-α}Γ(A)`, `ℓ > 0` and unit test `g`.
Counterexample: `d = 1`, `Γ` = Lebesgue measure (`α = 0`, outside `H:homog`
but inside the hypotheses of the general theorem), `ℓ = 2`: the package
identity gives `A_sp(U_2 g) = A_sp(g)`, the variant `2 A_sp(g)`, and
`A_sp(g) > 0` (`spatialEnergy_pos`).  `dilation_exponent_contrast` is the
package identity at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialSmoothRatio

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment HomogHypothesis SpatialFourierBound
  SpatialSmoothRatio

namespace Refutations.SpatialSmoothRatio

/-- Lebesgue measure on `ℝ¹` scales with `α = 0`. -/
theorem leb_scaling : VariationalDilation.SetScaling (0 : ℝ) (volume : Measure (Rd 1)) := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc]
  norm_num

/-- `A_sp(U_ℓ g) = ℓ^{α+1} A_sp(g)` is false. -/
theorem dilation_exponent_refuted :
    ¬ (∀ (Γ : Measure (Rd 1)) [IsLocallyFiniteMeasure Γ] (alpha : ℝ),
        VariationalDilation.SetScaling alpha Γ → ∀ ℓ : ℝ, 0 < ℓ → ∀ g : Rd 1 → ℝ,
        IsUnitTest g →
        spatialEnergy Γ (WeakSobolev.dilL2 ℓ g) = ℓ ^ (alpha + 1) * spatialEnergy Γ g) := by
  intro h
  obtain ⟨g, hg⟩ := exists_unitTest 1
  have h1 := h volume 0 leb_scaling 2 two_pos g hg
  have h2 := spatialEnergy_dilL2 leb_scaling two_pos hg.1.continuous hg.2.1
  have hA := spatialEnergy_pos leb_scaling (NeZero.ne _) hg
  rw [h2, Real.rpow_zero, zero_add, Real.rpow_one] at h1
  linarith

/-- The package identity at the same point: `A_sp(U_2 g) = 2^0 A_sp(g)`. -/
theorem dilation_exponent_contrast {g : Rd 1 → ℝ} (hg : IsUnitTest g) :
    spatialEnergy volume (WeakSobolev.dilL2 2 g) = (2 : ℝ) ^ (0 : ℝ) * spatialEnergy volume g :=
  spatialEnergy_dilL2 leb_scaling two_pos hg.1.continuous hg.2.1

end Refutations.SpatialSmoothRatio
