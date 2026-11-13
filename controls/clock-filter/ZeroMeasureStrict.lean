module
public import StratonovichHAMAudit.ClockFilter
/-!
Negative control for `StratonovichHAMAudit.ClockFilter.strict_filter_integral`.
Wrong variant: the strict filtered-integral inequality without the hypothesis
`σ ≠ 0`, in the shape of the package conclusion, at θ = 1, σ = 0, w = 1. Both
integrals against the zero measure vanish, so the strict inequality is `0 < 0`.
The package theorem is put in context; at σ = 0 its hypothesis `σ ≠ 0` fails, so
it gives nothing.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
open MeasureTheory
example : (fun (θ : ℝ) (σ : Measure ℝ) (w : ℝ → ℝ) =>
    (∫ ell, 2 * θ / (2 * θ + ell) * w ell ∂σ) < ∫ ell, w ell ∂σ) 1 0 (fun _ => 1) := by
  have h := StratonovichHAMAudit.ClockFilter.strict_filter_integral 1 one_pos (0 : Measure ℝ)
  simp at h ⊢
