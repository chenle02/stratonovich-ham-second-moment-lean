module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, integration: the hypothesis-free wrappers (interface section 6), with items B
(`WickSpectral`), C (`WickBridge`, `WickMass`, `WickScaling`) and D (`WickStep4`, `WickMeasures`)
discharging the hypotheses of item E (`JointFixedOrder`, `JointTail`, `EnvelopeD3Wave`).  Main TeX
lines at revision edf7085f (book 1.1.3):
* `L:spatial-wick-measures` 1679-1694 (proof 1696-1848; Steps 2-3 by route (b), decision 4);
* `E:joint-temporal-tail` 1915-1921 (d = 3 Green-width removal by the spectral route,
  decision 8, instead of the weak convergence of Green measures at 1923-1926);
* the joint diagram limit of `L:joint-fixed-order` 1855-1858 (deterministic half; the `L²`
  construction 1949-1965 is not formalized);
* the named input `D1Upper.DiagramLimits` discharged for every `H:homog` covariance in
  d = 1, 2, 3 (the Riesz case of item A, `RieszDiagramLimitsHomog.diagramLimits_homog_one`, is the
  domination route of decision 3; this module gives all d by the Wick-measure route);
* decision 13: the unsmoothed d = 3 successors of L17's E3 bounds (TeX 2352-2394; the displays
  `E:theta-envelope` 2003-2006 and `E:crude-corrected` 1980-1984, proof Steps 1-2 1993-2053).
The route differences are disclosed in the docstrings of the modules cited.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WickSpectral
public import StratonovichHAMSecondMoment.WickBridge
public import StratonovichHAMSecondMoment.WickMass
public import StratonovichHAMSecondMoment.WickScaling
public import StratonovichHAMSecondMoment.WickMeasures
public import StratonovichHAMSecondMoment.JointFixedOrder
public import StratonovichHAMSecondMoment.JointTail
public import StratonovichHAMSecondMoment.EnvelopeD3Wave

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory

namespace StratonovichHAMSecondMoment.WickFinal

open HomogHypothesis (Rd HomogCovariance)
open WickInterface

/-- **`L:spatial-wick-measures`, whole** (`SpatialWickMeasuresTarget d`; TeX lines 1679-1694 at
revision edf7085f (book 1.1.3)), with no supplied input. -/
theorem spatial_wick_measures_l18 (d : ℕ) : SpatialWickMeasuresTarget d :=
  WickMeasures.spatial_wick_measures d (WickSpectral.spatial_positive_laplace d)
    (WickMass.wick_mass_bound d (WickSpectral.smoothed_laplace d)) (WickScaling.rho_scaling d)

/-- **`E:joint-temporal-tail`** (`JointTemporalTailTarget d`; TeX lines 1915-1921 at revision
edf7085f (book 1.1.3)), d = 1, 2, 3, with no supplied input. -/
theorem joint_temporal_tail_l18 (d : ℕ) : JointTemporalTailTarget d :=
  JointTail.joint_temporal_tail d (WickBridge.m8_m7_bridge d) (WickSpectral.spectral_spatial_w d)

/-- **The joint diagram limit of `L:joint-fixed-order`** (`JointDiagramLimitTarget d`; TeX lines
1855-1858 at revision edf7085f (book 1.1.3)), with no supplied input. -/
theorem joint_diagram_limit_l18 (d : ℕ) : JointDiagramLimitTarget d :=
  JointFixedOrder.joint_diagram_limit d (spatial_wick_measures_l18 d) (joint_temporal_tail_l18 d)

/-- **`DiagramLimits` with finite limits for every `H:homog` covariance**
(`DiagramLimitsHomogTarget d`; TeX lines 1855-1858 with 825-832 at revision edf7085f (book
1.1.3)), with no supplied input. -/
theorem diagramLimits_homog_l18 (d : ℕ) : DiagramLimitsHomogTarget d :=
  JointFixedOrder.diagramLimits_homog d (spatial_wick_measures_l18 d) (joint_temporal_tail_l18 d)

/-- **The named input `D1Upper.DiagramLimits` discharged** for every `H:homog` covariance in
d = 1, 2, 3 and every horizon `t > 0`: the common-spatial-width consequence (one noise width
`ε ↓ 0` at every vertex, after uniform removal of the temporal cutoff) of the convergence clause of
`L:joint-fixed-order` (TeX lines 1855-1858, the joint limit at arbitrary relative rates), in
the lemma 1853-1966, at revision edf7085f (book 1.1.3); the lemma is invoked in Step 3 of the
proof of `P:d1-upper`, line 5534. -/
theorem diagramLimits_l18 {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) {t : ℝ} (ht : 0 < t) :
    D1Upper.DiagramLimits d Γ α₀ t :=
  (diagramLimits_homog_l18 d hH t ht).1

/-- **`E:homogeneous-envelope` in d = 3 for `waveGreen 3`** (`HomogEnvelopeThreeTarget`; TeX lines
2352-2394 at revision edf7085f (book 1.1.3)), with no supplied input. -/
theorem homogeneous_envelope_diagrams_three_l18 : HomogEnvelopeThreeTarget :=
  EnvelopeD3Wave.homogeneous_envelope_diagrams_three' (WickSpectral.spectral_spatial_w 3)

/-- **`E:theta-envelope` in d = 3 for `waveGreen 3`** (`ThetaEnvelopeThreeTarget`; TeX: the
display 2003-2006, in Step 1 1993-2031, at revision edf7085f (book 1.1.3)), with no supplied
input. -/
theorem theta_envelope_diagrams_three_l18 : ThetaEnvelopeThreeTarget :=
  EnvelopeD3Wave.theta_envelope_diagrams_three' (WickSpectral.spectral_spatial_w 3)

/-- **The first inequality of `E:crude-corrected` for the diagram sums, in d = 3 for
`waveGreen 3`** (`CrudeCorrectedThreeTarget`; TeX: the display 1980-1984; its first inequality
derived in Step 2, 2036-2041; at revision edf7085f (book 1.1.3)), with no supplied input. -/
theorem crude_corrected_diagrams_three_l18 : CrudeCorrectedThreeTarget :=
  EnvelopeD3Wave.crude_corrected_diagrams_three' (WickSpectral.spectral_spatial_w 3)

end StratonovichHAMSecondMoment.WickFinal
