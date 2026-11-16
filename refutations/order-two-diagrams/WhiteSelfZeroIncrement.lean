/-
Refutation for the positive-increment hypothesis of the Lean lemma
`StratonovichHAMSecondMoment.OrderTwoDiagrams.whiteSpatial_self`
(main TeX lines 959-962 at 39f2597a: "the first factor `G_r` has spatial mass `r`,
while `G_{s-r}(0) = 1/2`", used only for `s > r`).

Wrong variant: the collapsed white self-pairing spatial part is `h_0/2` also
when the second increment `h_1` is `0`.  Counterexample: `h = (1, 0)`: the
Green kernel `g(0, 0) = ½ 1_{|0| < 0}` is zero, so the collapsed spatial part
vanishes, and `0 ≠ 1/2`.  `whiteSelfZeroIncrement_contrast` is the package value
at `h = (1, 1)`.
Class (b): Lean-route-only control (a hypothesis of an auxiliary lemma; the TeX
uses the fact only in the open simplex, where `h_1 > 0`).
No junk-value reliance (`g(0, ·) = 0` is the TeX's `1_{|y| < 0} = 0`).
(Integration, wave L13: retargeted from the removed smoothed-limit lemma
`tendsto_spatial_white_self`, whose `ε ↓ 0` limit is now
`WhiteCollapse.tendsto_diagram_white`; same counterexample.)

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OrderTwoDiagrams

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel OrderTwoDiagrams

namespace Refutations.OrderTwoDiagrams

/-- The pairing of two labels. -/
def Dsw : Fin 2 → Fin 2 := ![1, 0]

/-- It is a fixed-point-free involution. -/
theorem Dsw_mem : ∀ i, Dsw i ≠ i ∧ Dsw (Dsw i) = i := by decide

/-- The package: at `h = (1, 1)` the collapsed spatial part is `1 · 1/2`. -/
theorem whiteSelfZeroIncrement_contrast :
    WhiteCollapse.whiteSpatial 2 Dsw ![1, 1] = ENNReal.ofReal 1 * ENNReal.ofReal (1 / 2) :=
  whiteSpatial_self (m := 2) (Or.inr rfl) Dsw_mem (h := ![1, 1]) (by norm_num)

/-- With a zero second increment the value is not `1 · 1/2`. -/
theorem whiteSelfZeroIncrement_refuted :
    ¬ WhiteCollapse.whiteSpatial 2 Dsw ![1, 0] = ENNReal.ofReal 1 * ENNReal.ofReal (1 / 2) := by
  rw [whiteSpatial_two Dsw_mem ![1, 0] (fun _ => 0) measurable_const (fun x => ?_),
    lintegral_zero]
  · norm_num
  · simp [WhiteCollapse.greenProd, Fin.prod_univ_two, (predVal_self (Or.inr rfl) _).1,
      (predVal_self (m := 2) (Or.inr rfl) _).2, WhiteCollapse.g1]

end Refutations.OrderTwoDiagrams
