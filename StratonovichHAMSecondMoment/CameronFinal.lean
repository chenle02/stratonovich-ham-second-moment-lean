module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16 integration: the item targets with every landed item output substituted for its
hypothesis.  This module proves nothing new; it only applies

* A1 `UniformMeanCutoff.uniform_cutoff`, `sobolev_embed`, `uniform_spatial_mean`;
* A2 `CameronProducts.cameron_fractional_products`;
* B2 `CameronSpatial.spatial_mean_map`, `cameron_spatial_map`;
* C `CameronTemporal.cameron_temporal_map` (hypothesis-free; the fallback `TemporalCompact` is
  not used), `young`, `kform_abs`;
* D `UniformMeanDischarge.positive_raw_embedding_of_products`, `uniform_mean_regulator_of`,
  `positive_raw_mean_of`.

Remaining named input (Le's decision for L16): `CutoffCompact d`, the compactness sentence of
`P:cutoff-singular-values` (`integrated_compact_gaussian.tex` lines 469-472 at revision edf7085f
(book 1.1.3)), used only by the compactness half of `P:cameron-spatial-map` and hence by the
regulator.  `positive_raw_embedding_paper_l16` and `spatial_mean_map_paper` need no named input.

TeX anchors (revision edf7085f, book 1.1.3): `integrated_cameron_mean.tex` lines 29-42
(`L:cameron-fractional-products`, proof 44-99), 104-119 (`P:cameron-spatial-map`, proof
121-186), 225-237 (`P:cameron-temporal-map`, proof 239-314); `integrated_uniform_mean.tex`
lines 272-288 (`P:uniform-mean-regulator`, proof 290-334); `integrated_intrinsic_constant.tex`
lines 22-40 (`L:positive-raw-embedding`, `E:positive-raw-mean` lines 34-37, proof 42-132).

No `sorry`, no axiom, no instance.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronProducts
public import StratonovichHAMSecondMoment.CameronTemporalTarget
public import StratonovichHAMSecondMoment.UniformMeanDischarge

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace StratonovichHAMSecondMoment.CameronFinal

open HomogHypothesis (Rd HomogCovariance)
open OccupationCompletion (TParams SpData)
open UniformMeanInterface
open CameronInterface

variable {d : ℕ}

/-- **`L:cameron-fractional-products` in the form B2 and D take it** (`integrated_cameron_mean.tex`
lines 29-42, proof 44-99, at revision edf7085f (book 1.1.3)): A2's theorem for every
`α/4 < s < 1/2`. -/
theorem fractional_products_all {alpha : ℝ} :
    ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s :=
  fun _ hs hs' => CameronProducts.cameron_fractional_products hs hs'

/-- **`P:cameron-spatial-map`, bounded part, nothing supplied** (`integrated_cameron_mean.tex`
lines 104-119, proof 121-186, at revision edf7085f (book 1.1.3)): the spatial mean map `T_R`
with the smooth-test formula and the row identity at all states for every `α/4 < s < 1/2`,
under `H:homog`.  A1 and A2 discharged; no compactness used. -/
theorem spatial_mean_map_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (η : CutoffProfile d) :
    SpatialMeanMapTarget hH η :=
  CameronSpatial.spatial_mean_map UniformMeanCutoff.uniform_cutoff
    UniformMeanCutoff.sobolev_embed fractional_products_all hH η

/-- **`P:cameron-spatial-map`, compact part** (`integrated_cameron_mean.tex` lines 104-119, proof
121-186, at revision edf7085f (book 1.1.3)): a `CameronSpatialMap` (compact `T_sp` with compact
values) whose row identity holds at all states for every `α/4 < s < 1/2`.  A1 and A2
discharged; the only named input is `CutoffCompact d` (`P:cutoff-singular-values`,
`integrated_compact_gaussian.tex` lines 469-472). -/
theorem cameron_spatial_map_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (η : CutoffProfile d) (hc : CutoffCompact d) :
    CameronSpatialTarget hH η :=
  CameronSpatial.cameron_spatial_map UniformMeanCutoff.uniform_cutoff
    UniformMeanCutoff.sobolev_embed fractional_products_all hH η hc

/-- **`L:positive-raw-embedding` with nothing supplied** (`integrated_intrinsic_constant.tex`
lines 22-40, `E:positive-raw-mean` lines 34-37, proof 42-132, at revision edf7085f (book
1.1.3)): under `H:homog` with `Γ ≠ 0`, for `2 < r < 2/α₀` there are constructed spatial mean
maps `T_R` (`R ≥ 1`) and a constructed `U` with `E:positive-raw-mean`.  A1, A2, B2 and C's
Young and `kform_abs` discharged; no compactness statement (B1, C) is used. -/
theorem positive_raw_embedding_paper_l16 {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] :
    PositiveRawEmbeddingTarget hH η r :=
  UniformMeanDischarge.positive_raw_embedding_of_products hH hΓ η fractional_products_all

/-- **`P:uniform-mean-regulator`, first bound and value class: the constructed regulator**
(`integrated_uniform_mean.tex` lines 272-288, proof 290-334, at revision edf7085f (book 1.1.3)):
under `H:homog` with `Γ ≠ 0`, for `2 < r < 2/α₀` a `UniformMeanRegulator` exists.  A1, A2, B2,
C (`cameron_temporal_map`, Young, `kform_abs`) and D discharged; the only named input is
`CutoffCompact d` (`P:cutoff-singular-values`, `integrated_compact_gaussian.tex` lines
469-472). -/
theorem uniform_mean_regulator_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hc : CutoffCompact d) :
    UniformMeanRegulatorTarget hH η r := fun hr2 hra =>
  UniformMeanDischarge.uniform_mean_regulator_of hH hΓ η fractional_products_all hc
    (CameronTemporal.cameron_temporal_map (TParams.ofHomog hH) hr2 hra) hr2 hra

/-- **The mean identity of `E:positive-raw-mean`, its canonical version and the compact value
class for the constructed regulator** (`integrated_intrinsic_constant.tex` lines 34-39: the
second identity of the display 34-37 and the canonical-version sentence 38-39; the first
identity `‖Ψ‖²_{H_I} = v_Ψ` is `OccupationCompletion.norm_incl_sq`; `integrated_uniform_mean.tex`
lines 279-280; at revision edf7085f (book 1.1.3)): L15's `positive_raw_mean_paper` applied to the
regulator of `uniform_mean_regulator_paper`, whose mean also takes compact values a.e.  The
only named input is `CutoffCompact d`. -/
theorem positive_raw_mean_paper_l16 {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hc : CutoffCompact d)
    (hr2 : 2 < r) (hra : r < ENNReal.ofReal (2 / alpha0)) :
    ∃ Ureg : UniformMeanRegulator (TParams.ofHomog hH) (SpData.ofHomog hH) η r,
      PositiveRawMeanTarget Ureg ∧ MeanCompactValuesTarget Ureg :=
  UniformMeanDischarge.positive_raw_mean_of hH hΓ η fractional_products_all hc
    (CameronTemporal.cameron_temporal_map (TParams.ofHomog hH) hr2 hra) hr2 hra

end StratonovichHAMSecondMoment.CameronFinal
