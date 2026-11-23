module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, integration (interface section 6; approved by Le on 2026-11-22 with the default answers
to all thirteen decisions): the hypothesis-free wrappers of the item targets of
`P:mild-construction` (A `MildOccupied`, B `MildPolyMem`, C `MildFields`, D
`MildTerminalFubini`/`MildPartialVertex`, E `MildGreenWidth`, F `MildConstruction`) and the M9
non-vacuity instance.  Main TeX file at revision edf7085f (book 1.1.3):
* `P:mild-construction` 2151-2165 (`E:mild-construction` 2156-2161), proof 2171-2340:
  Step 1 2187-2201 (`E:occupied-multiplication` 2189-2191, closure 2197-2201), 2181-2185 (the
  spaces `P_(<=n)`), Step 2 2204-2230, Step 3 2236-2265 with 4276-4285 (terminal Fubini
  2257-2260), Step 4 2268-2287, Step 5 2290-2303 (`E:external-vertex-limit` 2295-2297), Step 6
  2307-2339.

Every item target is discharged by the item theorem, every target-Prop hypothesis of an item
theorem by another item theorem; no named input remains (the fallbacks `TerminalFubini` and
`JointMeasurability` of the interface are not used).  Route differences are those disclosed in
the item modules: notably E's common-noise representation of the smoothed Green measure
(decision 3; stated for d = 1, 2, 3, the d = 1, 2 cases extra), and F's `mild_construction`
does not use B and C beyond their entry through D (`MildConstruction.mild_construction_of`).
The Riesz instance of `H:homog` (item R) and the hypothesis-free Riesz wrappers are in item W's
module `CleanupWrappers` (`riesz_instance_l20`, the `…_closed_l20` forms) and are not repeated
here.  Hypothesis kept, as the TeX states it: `H:homog` (`HomogCovariance`), inside each target
except A's `OccupiedMultTarget` (stated for any centered Gaussian field).
No instance is declared.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface
public import StratonovichHAMSecondMoment.MildOccupied
public import StratonovichHAMSecondMoment.MildPolyMem
public import StratonovichHAMSecondMoment.MildFields
public import StratonovichHAMSecondMoment.MildTerminalFubini
public import StratonovichHAMSecondMoment.MildPartialVertex
public import StratonovichHAMSecondMoment.MildGreenWidth
public import StratonovichHAMSecondMoment.MildConstruction

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace StratonovichHAMSecondMoment.MildFinal

universe u v

open MildInterface

/-! ### Hypothesis-free item targets -/

/-- **`E:occupied-multiplication` and the closedness of multiplication** (`OccupiedMultTarget`;
Step 1, TeX 2187-2201 at revision edf7085f (book 1.1.3)): item A, for every centered Gaussian
field. -/
theorem occupied_mult_l20 : OccupiedMultTarget.{u, v} :=
  MildOccupied.occupied_mult

/-- **The terminal integrals and their limits lie in `P_(<=n)`** (`PolyMemTarget`; TeX 2181-2185
at revision edf7085f (book 1.1.3)): item B. -/
theorem poly_mem_l20 (d : ℕ) : PolyMemTarget.{u} d :=
  MildPolyMem.poly_mem d

/-- **Joint measurability, stationarity and spatial continuity of the fields** (`FieldMeasTarget`;
Step 2, TeX 2204-2230 at revision edf7085f (book 1.1.3)): item C, with no named input. -/
theorem field_meas_l20 (d : ℕ) : FieldMeasTarget.{u} d :=
  MildFields.field_meas d

/-- **The last-vertex (terminal) Fubini identity** (`TerminalFubiniTarget`; TeX 2257-2260 with
4276-4285 at revision edf7085f (book 1.1.3)): item D. -/
theorem terminal_fubini_l20 (d : ℕ) : TerminalFubiniTarget.{u} d :=
  MildTerminalFubini.terminal_fubini d

/-- **`E:partial-vertex-limit`** (`PartialVertexTarget`; Step 3, TeX 2236-2265 at revision
edf7085f (book 1.1.3)): item D with A, B, C and the terminal Fubini identity discharged. -/
theorem partial_vertex_l20 (d : ℕ) : PartialVertexTarget.{u} d :=
  MildPartialVertex.partial_vertex d occupied_mult_l20.{u, 0} (poly_mem_l20 d) (field_meas_l20 d)
    (terminal_fubini_l20 d)

/-- **The Green-width limit of the mild integrals** (`GreenWidthMildTarget`; Step 4, TeX
2268-2287 with 2162-2164, 2167-2169, 2327-2328 at revision edf7085f (book 1.1.3)): item E with A,
B, C, D discharged.  Route difference (decision 3): the common-noise representation of the
smoothed Green measure; stated for d = 1, 2, 3 (the TeX's convention is d = 3). -/
theorem green_width_mild_l20 (d : ℕ) : GreenWidthMildTarget.{u} d :=
  MildGreenWidth.green_width_mild d occupied_mult_l20.{u, 0} (poly_mem_l20 d) (field_meas_l20 d)
    (partial_vertex_l20 d)

/-- **`E:external-vertex-limit`** (`ExternalVertexTarget`; Step 5, TeX 2290-2303 at revision
edf7085f (book 1.1.3)): item F with D discharged. -/
theorem external_vertex_l20 (d : ℕ) : ExternalVertexTarget.{u} d :=
  MildConstruction.external_vertex d (partial_vertex_l20 d)

/-- **`P:mild-construction`, `E:mild-construction`** (`MildConstructionTarget`; TeX 2151-2165,
display 2156-2161, proof Steps 1-6 2178-2339 at revision edf7085f (book 1.1.3)): under `H:homog`,
for every source field, `t > 0` and `x`, `W_a u ∈ L²` pointwise, the mild integrand is integrable
against the mild (Green) measure, and the mild integral tends to `u(t,x) - 1` in `L²` as
`ε, δ ↓ 0` at arbitrary relative rates.  Item F's frozen theorem with A, B, C, D and Step 5
discharged. -/
theorem mild_construction_l20 (d : ℕ) : MildConstructionTarget.{u} d :=
  MildConstruction.mild_construction d occupied_mult_l20.{u, 0} (poly_mem_l20 d)
    (field_meas_l20 d) (partial_vertex_l20 d) (external_vertex_l20 d)

/-! ### Non-vacuity at the constructed model M9 -/

/-- **`P:mild-construction` at M9** (gate non-vacuity; TeX 2151-2165 at revision edf7085f (book
1.1.3)): the mild-equation limit holds for the solution built on L19's constructed source field
`m9 (SourceFinal.source_field_l19 d) hH`, under `H:homog`. -/
theorem mild_construction_m9_l20 (d : ℕ) : MildConstructionM9 d :=
  mildConstructionM9_of (mild_construction_l20.{0} d)

end StratonovichHAMSecondMoment.MildFinal
