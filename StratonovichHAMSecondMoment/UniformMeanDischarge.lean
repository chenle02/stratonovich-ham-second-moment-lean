module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-D, part 4: the D targets with the other items' landed outputs substituted
for their hypotheses (merged from `wave-l16/a`, `/b`, `/c`).  The hypothesis-form theorems of
`CameronUMap` and `UniformMeanAssembly` are unchanged; this module only applies them.

TeX anchors (revision edf7085f, book 1.1.3): `integrated_uniform_mean.tex`
lines 257-334 (`U`, `P:uniform-mean-regulator`), `integrated_intrinsic_constant.tex` lines
22-132 (`L:positive-raw-embedding`).

Discharged here (item outputs used):
* `UniformMeanCutoff.uniform_cutoff`, `sobolev_embed`, `uniform_spatial_mean` (A1);
* `CameronSpatial.spatial_mean_map`, `cameron_spatial_map` (B2);
* `CameronTemporal.young`, `kform_abs` (C).

Hypotheses still open in this module (their items have not landed a theorem of the frozen
signature on the merged branches): `FractionalProductsTarget` (A2's
`cameron_fractional_products`), `CutoffCompact d` (B1's `cutoffCompact`, or the named input)
and `TemporalMapTarget` (C's `cameron_temporal_map`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.UniformMeanAssembly
public import StratonovichHAMSecondMoment.UniformMeanCutoff
public import StratonovichHAMSecondMoment.CameronSpatial
public import StratonovichHAMSecondMoment.CameronTemporalYoung

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace StratonovichHAMSecondMoment.UniformMeanDischarge

open HomogHypothesis (Rd HomogCovariance)
open OccupationCompletion (TParams SpData)
open UniformMeanInterface
open CameronInterface

variable {d : ℕ}

/-- **D target 2 with C's lemmas discharged: `U` with `‖U‖ ≤ ‖C_t‖`** (`UMapTarget`,
`integrated_uniform_mean.tex` lines 257-270 and 312-313 at revision edf7085f (book
1.1.3)); kernel-positivity route (`CameronUMap.u_map`). -/
theorem u_map_paper (p : TParams) (S : SpData d) (r : ℝ≥0∞) [Fact (1 ≤ r)] :
    UMapTarget p S r :=
  CameronUMap.u_map p S r CameronTemporal.young (CameronTemporal.kform_abs p)

/-- **D target 4 with A1, B2 and C discharged: `L:positive-raw-embedding` for the constructed
maps** (`integrated_intrinsic_constant.tex` lines 22-40, proof 42-132, at revision edf7085f
(book 1.1.3)), under `H:homog` with `Γ ≠ 0`.  The only remaining hypothesis is A2's
`L:cameron-fractional-products` (`FractionalProductsTarget`), which B2's `spatial_mean_map`
takes.  No compactness statement is used. -/
theorem positive_raw_embedding_of_products {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s) :
    PositiveRawEmbeddingTarget hH η r :=
  UniformMeanAssembly.positive_raw_embedding_constructed hH hΓ η
    (CameronSpatial.spatial_mean_map UniformMeanCutoff.uniform_cutoff
      UniformMeanCutoff.sobolev_embed hA2 hH η)
    CameronTemporal.young (CameronTemporal.kform_abs _)

/-- **D target 3 with A1, B2, C (Young, `kform_abs`) and D discharged:
`P:uniform-mean-regulator`, first bound and value class** (`integrated_uniform_mean.tex` lines
272-288, proof 290-318, at revision edf7085f (book 1.1.3)).  Remaining hypotheses:
A2's `FractionalProductsTarget`, B1's `CutoffCompact` (taken by B2's `cameron_spatial_map`) and
C's `TemporalMapTarget`. -/
theorem uniform_mean_regulator_of {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s)
    (hc : CutoffCompact d) (hC : TemporalMapTarget (TParams.ofHomog hH) r) :
    UniformMeanRegulatorTarget hH η r :=
  UniformMeanAssembly.uniform_mean_regulator hH hΓ η
    (CameronSpatial.cameron_spatial_map UniformMeanCutoff.uniform_cutoff
      UniformMeanCutoff.sobolev_embed hA2 hH η hc)
    (UniformMeanCutoff.uniform_spatial_mean _) UniformMeanCutoff.uniform_cutoff
    UniformMeanCutoff.sobolev_embed hA2 hC (u_map_paper _ _ r)

/-- **The mean identity of `E:positive-raw-mean`, its canonical version and the compact value
class for a constructed regulator, item outputs discharged** (`integrated_intrinsic_constant.tex`
lines 32-39 at revision edf7085f (book 1.1.3); the first identity `‖Ψ‖²_{H_I} = v_Ψ` is
`OccupationCompletion.norm_incl_sq`):
L15's `positive_raw_mean_paper` applied to the regulator of `uniform_mean_regulator_of`.
Remaining hypotheses as there. -/
theorem positive_raw_mean_of {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s)
    (hc : CutoffCompact d) (hC : TemporalMapTarget (TParams.ofHomog hH) r)
    (hr2 : 2 < r) (hra : r < ENNReal.ofReal (2 / alpha0)) :
    ∃ Ureg : UniformMeanRegulator (TParams.ofHomog hH) (SpData.ofHomog hH) η r,
      PositiveRawMeanTarget Ureg ∧ MeanCompactValuesTarget Ureg := by
  obtain ⟨Ureg⟩ := uniform_mean_regulator_of hH hΓ η hA2 hc hC hr2 hra
  exact ⟨Ureg, PositiveRawMean.positive_raw_mean_paper hH hΓ η Ureg,
    UniformMeanAssembly.mean_compact_values Ureg⟩

end StratonovichHAMSecondMoment.UniformMeanDischarge
