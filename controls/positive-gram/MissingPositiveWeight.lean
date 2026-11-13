module
public import StratonovichHAMAudit.PositiveGram
/-!
Negative control for `StratonovichHAMAudit.PositiveGram.scalar_sqrt_dual`.
Wrong variant: the scalar square-root duality bound without the hypothesis `0 < w`,
in the exact shape of the package statement, at ell = 1, w = 0, t = 1. With Lean's
junk value `1 / 0 = 0` the claim becomes `2 ≤ 0`. The package theorem is put in
context; its hypothesis `0 < w` fails at w = 0, so it gives nothing.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
example : (fun ell w t : ℝ => 2 * ell * Real.sqrt t ≤ ell ^ 2 / w + w * t) 1 0 1 := by
  have h := StratonovichHAMAudit.PositiveGram.scalar_sqrt_dual 1 0 1
  norm_num at h ⊢
