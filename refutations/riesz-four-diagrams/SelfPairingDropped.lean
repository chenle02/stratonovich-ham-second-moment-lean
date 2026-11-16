/-
Refutation for the order-two Riesz diagram limit (the formerly supplied input
`RieszDiagramLimit`, main TeX lines 825-832 and 5129-5134 at 39f2597a: the TeX's
`J_{2,0,D}(t)` for `Γ(dy) = c|y|^{-α} dy` is the density diagram, value
`c t^β/((1-α)(2-α-α₀)(3-α-α₀)(4-α-α₀))`), package theorems
`StratonovichHAMSecondMoment.RieszFourDiagrams.rieszDiagramLimit` and
`riesz_small_paper'`.

Wrong variant: the self-pairing of one chain drops out in the limit of the
smoothed diagrams (the Skorohod convention, where `E X_2 = 0`), i.e. the
measure-form diagram `J_{2,0,D}(1)` is `0`.  Counterexample: `c = 1`,
`α = α₀ = 1/2`, `t = 1`: the limit is `1/3`.  `selfPairingDropped_contrast` is
the package value at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszFourDiagrams

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel OrderTwoDiagrams RieszFourDiagrams

namespace Refutations.RieszFourDiagrams

/-- The package: at `c = 1`, `α = α₀ = 1/2`, `t = 1` the measure-form `(2,0)` Riesz
diagram is `1/3`. -/
theorem selfPairingDropped_contrast :
    ∀ D ∈ Pi2 2 0, diagramLim 1 ((volume : Measure (HomogHypothesis.Rd 1)).withDensity
      (HigherRieszTwo.riesz 1 (1 / 2))) (1 / 2) 2 0 D 1 = ENNReal.ofReal (1 / 3) := by
  intro D hD
  rw [rieszDiagramLimit zero_le_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    zero_le_one 2 0 D rfl hD, riesz_self_two_zero hD zero_le_one (by norm_num) (by norm_num)
    zero_le_one, Real.one_rpow]
  congr 1
  norm_num

/-- The self-pairing does not drop out. -/
theorem selfPairingDropped_refuted :
    ¬ ∀ D ∈ Pi2 2 0, diagramLim 1 ((volume : Measure (HomogHypothesis.Rd 1)).withDensity
      (HigherRieszTwo.riesz 1 (1 / 2))) (1 / 2) 2 0 D 1 = 0 := by
  intro h
  obtain ⟨D, hD⟩ : (Pi2 2 0).Nonempty :=
    Finset.card_pos.1 (by rw [card_Pi2 (m := 2) (n := 0) (k := 1) rfl]; decide)
  have h1 := h D hD
  rw [selfPairingDropped_contrast D hD, ENNReal.ofReal_eq_zero] at h1
  norm_num at h1

end Refutations.RieszFourDiagrams
