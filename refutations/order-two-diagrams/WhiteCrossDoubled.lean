/-
Refutation for the cross diagram of `L:white-test` (main TeX lines 940-949 and
952-958 at 39f2597a: "`∫ G(s,y) G(r,y) dy = min(s,r)/2`. The `(1,1)` integral is
`c_0 t^{3-α₀}`"), package theorem
`StratonovichHAMSecondMoment.OrderTwoDiagrams.white_cross`.

Wrong variant: the `(1,1)` diagram equal to `2 c_0 t^{3-α₀}` (the value obtained
with `∫ G_s G_r = min(s,r)` instead of `min(s,r)/2`, or by assigning the whole
total-order-two contribution to the cross term).  Counterexample: `α₀ = 1/2`,
`t = 1`: the diagram is `c_0 > 0`, not `2 c_0`.  `whiteCrossDoubled_contrast` is
the package value at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance (`c_0(1/2) = 8/15 > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OrderTwoDiagrams

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel OrderTwoDiagrams

namespace Refutations.OrderTwoDiagrams

/-- The package: at `α₀ = 1/2`, `t = 1` every `(1,1)` white diagram is `c_0`. -/
theorem whiteCrossDoubled_contrast :
    ∀ D ∈ Pi2 1 1, diagramLim 1 (Measure.dirac 0) (1 / 2) 1 1 D 1 =
      ENNReal.ofReal (c0 (1 / 2)) := by
  intro D hD
  rw [white_cross hD (by norm_num) zero_le_one, Real.one_rpow, mul_one]

/-- The doubled value is false. -/
theorem whiteCrossDoubled_refuted :
    ¬ ∀ D ∈ Pi2 1 1, diagramLim 1 (Measure.dirac 0) (1 / 2) 1 1 D 1 =
      ENNReal.ofReal (2 * c0 (1 / 2)) := by
  intro h
  obtain ⟨D, hD⟩ : (Pi2 1 1).Nonempty :=
    Finset.card_pos.1 (by rw [card_Pi2 (m := 1) (n := 1) (k := 1) rfl]; decide)
  have h1 := h D hD
  rw [whiteCrossDoubled_contrast D hD] at h1
  have hc := c0_pos (α₀ := 1 / 2) (by norm_num)
  rw [ENNReal.ofReal_eq_ofReal_iff hc.le (by linarith)] at h1
  linarith

end Refutations.OrderTwoDiagrams
