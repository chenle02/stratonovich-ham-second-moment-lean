/-
Refutation for the `L¹` bound on the Fourier transform of `SpatialFourierBound`,
package theorem
`StratonovichHAMSecondMoment.SpatialFourierBound.norm_fourierQ_le`
(`|Q̂(ξ)| ≤ ‖Q‖₁`, the first pointwise bound behind `|Q̂|² ≤ min(1, 4b/|ξ|²)`
in the deterministic bound for `P:spatial-smooth-ratio`,
`notes/integrated_spatial_occupation.tex` lines 166-170 at a284420).

Wrong variant: `|Q̂(ξ)| ≤ ‖Q‖₁/2` for every real `Q` and `ξ`.
Counterexample: `d = 1`, `Q = g²` for a real unit test `g` (a normalized bump,
`SpatialSmoothRatio.exists_unitTest`), `ξ = 0`: `Q̂(0) = ∫ Q = 1` while
`‖Q‖₁/2 = 1/2`.  `fourier_norm_half_contrast` is the package bound at the same
point (`1 ≤ 1`).
No junk-value reliance (`Q` is continuous with compact support, so every
integral here is a genuine integral).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialFourierBound
import StratonovichHAMSecondMoment.SpatialSmoothRatio

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment HomogHypothesis SpatialFourierBound

namespace Refutations.SpatialFourierBound

/-- Auxiliary: `Q̂(0) = ∫ Q` and `‖Q‖₁ = ∫ Q = 1` for `Q = g²`, `g` a unit test. -/
theorem fourier_zero {g : Rd 1 → ℝ} (hg : IsUnitTest g) :
    ‖fourierQ (fun x => g x ^ 2) 0‖ = 1 ∧ ∫ x, |g x ^ 2| = 1 := by
  have h1 : ∫ x, |g x ^ 2| = 1 := by
    simp_rw [abs_pow, sq_abs]; exact hg.2.2
  refine ⟨?_, h1⟩
  simp only [fourierQ, inner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one]
  rw [integral_complex_ofReal, hg.2.2]
  simp

/-- `|Q̂(ξ)| ≤ ‖Q‖₁/2` is false. -/
theorem fourier_norm_half_refuted :
    ¬ (∀ (Q : Rd 1 → ℝ) (ξ : Rd 1), ‖fourierQ Q ξ‖ ≤ (∫ x, |Q x|) / 2) := by
  intro h
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest 1
  have h1 := h (fun x => g x ^ 2) 0
  obtain ⟨e1, e2⟩ := fourier_zero hg
  rw [e1, e2] at h1
  norm_num at h1

/-- The package bound at the same point: `1 ≤ 1`. -/
theorem fourier_norm_half_contrast {g : Rd 1 → ℝ} (hg : IsUnitTest g) :
    ‖fourierQ (fun x => g x ^ 2) 0‖ ≤ ∫ x, |g x ^ 2| ∧ ∫ x, |g x ^ 2| = 1 :=
  ⟨norm_fourierQ_le _ 0, (fourier_zero hg).2⟩

end Refutations.SpatialFourierBound
