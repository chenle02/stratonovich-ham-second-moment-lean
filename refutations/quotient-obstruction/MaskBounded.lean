/-
Refutation for `P:masked-quotient-obstruction`
(`notes/integrated_covariance_foundation.tex` lines 257-292 at a284420), package
theorem
`StratonovichHAMSecondMoment.QuotientObstruction.masked_quotient_obstruction_paper`.

Wrong variant: "a physical mask preserves noise-null tests": for every real
compact smooth `ζ` there is a finite `C` with `E W(ζF)² ≤ C E W(F)²` for every
test `F` (here at `d = 2`, `α = 1`, `a = 1/2`, `T = 1`, `Γ = δ₀(dx₁) dx₂`, with
`E W(F)²` the covariance functional `covW`).
Counterexample: the package's `ζ = χ ⊗ χ`; `mask_bounded_contrast` exhibits the
test `F = τ ⊗ (χ ⊗ χ'')` with `E W(F)² = 0 < E W(ζF)²`.
No junk-value reliance (the package proves the integrability of every integrand
it evaluates).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.QuotientObstruction

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff
open StratonovichHAMSecondMoment HomogHypothesis QuotientObstruction

namespace Refutations.QuotientObstruction

/-- "Every compact smooth mask is bounded on the noise variance" is false. -/
theorem mask_bounded_refuted :
    ¬ (∀ ζ : Rd 2 → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
        ∃ C : ℝ, ∀ F : ℝ → Rd 2 → ℝ, IsTest 1 F →
          covW (1 / 2) Gamma0 (fun t x => ζ x * F t x) ≤ C * covW (1 / 2) Gamma0 F) := by
  intro h
  obtain ⟨-, -, ζ, hζ, hζc, hn⟩ :=
    masked_quotient_obstruction_paper (a := 1 / 2) (by norm_num) (by norm_num) (T := 1) one_pos
  exact hn (h ζ hζ hζc)

/-- The package witnesses at the same point: a test with zero unmasked and
positive masked variance. -/
theorem mask_bounded_contrast :
    ∃ τ : ℝ → ℝ, IsTest 1 (fun t x => τ t * gtest x) ∧
      covW (1 / 2) Gamma0 (fun t x => τ t * gtest x) = 0 ∧
      0 < covW (1 / 2) Gamma0 (fun t x => zeta x * (τ t * gtest x)) := by
  obtain ⟨τ, hF, -, -, -, -, -, -, h0, -, hpos⟩ :=
    masked_quotient_obstruction (a := 1 / 2) (by norm_num) (by norm_num) (T := 1) one_pos
  exact ⟨τ, hF, h0, hpos⟩

end Refutations.QuotientObstruction
