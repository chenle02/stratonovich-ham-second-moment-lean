/-
Refutation for the positivity part of `P:spatial-smooth-ratio`
(`notes/integrated_spatial_occupation.tex` lines 168-170 and 186-187 at a284420),
package theorem `StratonovichHAMSecondMoment.SpatialSmoothRatio.R0_pos_finite`
(`0 < R_0`, under `Γ ≠ 0`, the section's standing assumption, line 4).

Wrong variant: the hypothesis `Γ ≠ 0` dropped, i.e. `0 < R_0` for every locally
finite `Γ` with a homogeneous spectral measure and `Γ(cA) = c^{d-α}Γ(A)`.
Counterexample: `d = 1`, `Γ = μ = 0`, `α = 1`: all hypotheses hold, every
`A_sp(g)` is `0`, so the ratio set is `{0}` (nonempty by `exists_unitTest`) and
`R_0 = sup {0} = 0`.  `drop_gamma_nonzero_contrast` records `R_0 = 0` there;
the package theorem cannot be applied (its hypothesis `Γ ≠ 0` fails).
No junk-value reliance: `R_0` is the supremum of the nonempty bounded set
`{0}` (the integral against the zero measure is genuinely `0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialSmoothRatio

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment HomogHypothesis SpatialFourierBound
  SpatialSmoothRatio

namespace Refutations.SpatialSmoothRatio

/-- `R_0 = 0` for the zero covariance. -/
theorem drop_gamma_nonzero_contrast : R0 (0 : Measure (Rd 1)) 1 = 0 := by
  have hset : ratioSet (0 : Measure (Rd 1)) 1 = {0} := by
    ext r
    constructor
    · rintro ⟨g, -, rfl⟩
      simp [ratio, spatialEnergy, spatialPair]
    · rintro rfl
      obtain ⟨g, hg⟩ := exists_unitTest 1
      exact ⟨g, hg, by simp [ratio, spatialEnergy, spatialPair]⟩
  rw [R0, hset, csSup_singleton]

/-- `0 < R_0` without `Γ ≠ 0` is false. -/
theorem drop_gamma_nonzero_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)) [IsLocallyFiniteMeasure Γ] [IsLocallyFiniteMeasure μ],
        IsSpectralMeasure Γ μ → ∀ alpha : ℝ, SpectralHomog.SpectralHomogeneous μ alpha →
        VariationalDilation.SetScaling alpha Γ → alpha < 2 → 0 < R0 Γ alpha) := by
  intro h
  have h1 := h 0 0 (fun φ => by simp) 1 (fun A _ c _ => by simp)
    (fun A _ c _ => by simp) (by norm_num)
  rw [drop_gamma_nonzero_contrast] at h1
  exact lt_irrefl 0 h1

end Refutations.SpatialSmoothRatio
