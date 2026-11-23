/-
Refutation for the empty-chain convention of `DiagramModel` (main TeX lines 825
and 843 at edf7085f: "An empty chain contributes the factor one", "the case
`m = n = 0` equals one"; `A_0(t) = 1`, line 5448), package theorems
`StratonovichHAMSecondMoment.DiagramModel.diagramLim_zero_zero` and
`coeffALim_zero`.

Wrong variant: the diagram `J_{0,0}(t)` of two empty chains is `0` (an empty
time domain read as a null set).  Counterexample: `d = 1`, spatial white noise
`Γ = δ₀`, `α₀ = 1/2`, horizon `t = 1`, the empty pairing `D = id`.  This
instance is admissible: it satisfies `H:homog` (main TeX lines 384-401) in its
case `α = d = 1` ("spatial white noise `Γ = δ₀`", lines 399-400), with
`0 < α₀ = 1/2 < 1` (line 385) and the threshold `E:threshold`
`α₀ + α = 3/2 < 2` (lines 396-398), and `t = 1 > 0` lies in the time domain
`ℝ_+` of `E:HAM` (line 375; `t > 0` in `L:joint-fixed-order`, line 1858).
The package value, the limit `diagramLim` of the smoothed diagrams, is `1`.
`emptyDiagram_contrast` is the package value at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain (the zeroth
term `X_0 = 1` of `E:expansion`).
No junk-value reliance (the limit of the constant `1` is `1`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramModel

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel

namespace Refutations.DiagramModel

/-- The package: for `d = 1`, `Γ = δ₀`, `α₀ = 1/2`, `t = 1`, the empty diagram
`J_{0,0}(1)` is `1`. -/
theorem emptyDiagram_contrast :
    diagramLim 1 (Measure.dirac (0 : HomogHypothesis.Rd 1)) (1 / 2) 0 0 id 1 = 1 :=
  diagramLim_zero_zero _ _ _ _ _

/-- The empty diagram is not `0` at the same admissible point. -/
theorem emptyDiagram_refuted :
    ¬ (diagramLim 1 (Measure.dirac (0 : HomogHypothesis.Rd 1)) (1 / 2) 0 0 id 1 = 0) := by
  rw [emptyDiagram_contrast]; exact one_ne_zero

end Refutations.DiagramModel
