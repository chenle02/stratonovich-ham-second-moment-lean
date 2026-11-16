/-
Refutation for the normalization of `E:riesz-four` (main TeX lines 5157-5163 and
5201-5204 at 39f2597a: "the factors `1/16` are already incorporated in the four
uniform probability laws"), package theorems
`StratonovichHAMSecondMoment.RieszFourDiagrams.riesz_four` and `diagram_riesz_eq`.

Wrong variant: the Green factors `½` are counted a second time, i.e.
`J_{m,n,D}(t) = c^2 t^{2β} I_{m,D}/16`.  Counterexample: `c = 1`, `α = α₀ = 1/2`,
`t = 1`, the split `(4,0)`: the diagram equals `I_{4,D}`, which is positive and
finite (`diagram_riesz_pos`, `rieszUnit_ne_top`), so it is not `I_{4,D}/16`.
`uniformNormalizationTwice_contrast` is the package representation at the same
point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszFourDiagrams

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel RieszFourDiagrams

namespace Refutations.RieszFourDiagrams

/-- The package: at `c = 1`, `α = α₀ = 1/2`, `t = 1`, `(m, n) = (4, 0)`. -/
theorem uniformNormalizationTwice_contrast :
    ∀ D ∈ Pi2 4 0, diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2)
      4 0 D 1 = ENNReal.ofReal ((1 : ℝ) ^ 2 * (1 : ℝ) ^ (2 * (4 - 1 / 2 - 1 / 2 : ℝ))) *
        rieszUnit (1 / 2) (1 / 2) 4 0 D :=
  fun D hD => ((riesz_four zero_le_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (m := 4) (n := 0) rfl one_pos).2 D hD).1

/-- The uniform laws already carry the factors `1/16`. -/
theorem uniformNormalizationTwice_refuted :
    ¬ ∀ D ∈ Pi2 4 0, diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2)
      4 0 D 1 = ENNReal.ofReal ((1 : ℝ) ^ 2 * (1 : ℝ) ^ (2 * (4 - 1 / 2 - 1 / 2 : ℝ))) *
        (rieszUnit (1 / 2) (1 / 2) 4 0 D / 16) := by
  intro h
  obtain ⟨D, hD⟩ : (Pi2 4 0).Nonempty :=
    Finset.card_pos.1 (by rw [card_Pi2 (m := 4) (n := 0) (k := 2) rfl]; decide)
  have h1 := h D hD
  have h2 := uniformNormalizationTwice_contrast D hD
  have hpos := diagram_riesz_pos (c := 1) (α := 1 / 2) (α₀ := 1 / 2) one_pos (by norm_num) D
    one_pos
  have htop := rieszUnit_ne_top (α := 1 / 2) (α₀ := 1 / 2) (m := 4) (n := 0) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (k := 2) rfl hD
  simp only [one_pow, Real.one_rpow, mul_one, ENNReal.ofReal_one, one_mul] at h1 h2
  rw [h2] at hpos h1
  have hr := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_div] at hr
  have hp : 0 < (rieszUnit (1 / 2) (1 / 2) 4 0 D).toReal := ENNReal.toReal_pos hpos.ne' htop
  norm_num at hr
  linarith

end Refutations.RieszFourDiagrams
