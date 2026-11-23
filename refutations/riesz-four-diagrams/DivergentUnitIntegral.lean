/-
Refutation for the finiteness clause of `E:riesz-four` (main TeX line 5169 at
edf7085f: "This is a finite nonnegative integral", proof lines 5213-5219), package
theorems `StratonovichHAMSecondMoment.RieszFourDiagrams.rieszUnit_ne_top` and
`diagram_riesz_ne_top`.

Wrong variant: for the cross split `(2,2)` the unit-domain integral diverges (a
skeptic's reading that the two spatial factors of a pairing joining both chains
are not integrable together).  Counterexample: `α = α₀ = 1/2`: every `(2,2)`
unit-domain integral is finite, and the corresponding diagram at `c = t = 1` is
positive.  `divergentUnitIntegral_contrast` is the package finiteness at the same
point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszFourDiagrams

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel RieszFourDiagrams

namespace Refutations.RieszFourDiagrams

/-- The package: at `α = α₀ = 1/2` every `(2,2)` unit-domain integral is finite, and
the diagram at `c = t = 1` is positive and finite. -/
theorem divergentUnitIntegral_contrast :
    ∀ D ∈ Pi2 2 2, rieszUnit (1 / 2) (1 / 2) 2 2 D ≠ ⊤ ∧
      0 < diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 2 2 D 1 ∧
      diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 2 2 D 1 ≠ ⊤ :=
  fun D hD => ⟨rieszUnit_ne_top (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (k := 2) rfl hD, diagram_riesz_pos one_pos (by norm_num) D one_pos,
    diagram_riesz_ne_top zero_le_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hD zero_le_one⟩

/-- The `(2,2)` unit-domain integrals do not diverge. -/
theorem divergentUnitIntegral_refuted :
    ¬ ∃ D ∈ Pi2 2 2, rieszUnit (1 / 2) (1 / 2) 2 2 D = ⊤ := by
  rintro ⟨D, hD, h⟩
  exact (divergentUnitIntegral_contrast D hD).1 h

end Refutations.RieszFourDiagrams
