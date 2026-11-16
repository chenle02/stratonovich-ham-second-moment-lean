import StratonovichHAMSecondMoment.FockSandwichModel

/-!
Refutation for `StratonovichHAMSecondMoment.FockSandwichModel.symI_mul_band` and
`invSqrtShift_band` (on the joint range, `invSqrtShift A_0 ρ` is `(ρ² - Δ)^{-1/2}`).

Wrong variant: claim the model's `(ρ² + |η|² 1_b)^{-1/2}` equals `(ρ² + |η|²)^{-1/2}`
everywhere, i.e. that `invSqrtShift A_0 ρ` is `A_ρ^{-1/2}` on all of the model space and not
only on the band range.  Counterexample: `ρ = 1`, `b = 0`, `|η| = 1`, where the two symbols
are `1` and `1/√2`.  Class (b): Lean-route-only control (the model works on the whole space,
with `A_0 = 0` off the band; the identification holds only after `S_b`).
`shifted_symbol_band_contrast` is the package identity after the band.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockSandwichModel

open StratonovichHAMSecondMoment.FockSandwichModel
open StratonovichHAMSecondMoment.FockColumnBound (wt band)
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- Off the band the model symbol is not the resolvent symbol. -/
theorem shifted_symbol_everywhere_refuted : ¬ ∀ η : Rd 1, symI 1 0 η = wt 1 η := by
  intro H
  have hn : ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : Rd 1)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp
  have hb : band (0 : ℝ) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : Rd 1) = 0 := by
    unfold band
    rw [Set.indicator_of_notMem]
    rw [Metric.mem_closedBall, dist_zero_right, hn]
    norm_num
  have h := H (EuclideanSpace.single 0 1)
  rw [symI, symS, symA, hb, wt, hn] at h
  norm_num at h

/-- Contrast: after the band the two symbols agree. -/
theorem shifted_symbol_band_contrast (ρ b : ℝ) (η : Rd 1) :
    symI ρ b η * band b η = band b η * wt ρ η :=
  symI_mul_band ρ b η

end Refutations.FockSandwichModel
