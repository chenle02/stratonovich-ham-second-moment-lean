module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item L18-0 (interface; approved by Le on 2026-11-21 with the default answers to all
thirteen decisions: scope L18-0, A..E; domination route for A; route (b) (envelope, damped norms
and scaling) for Steps 2-3 of `L:spatial-wick-measures`; model M8; `L:joint-fixed-order`
narrower (deterministic half); d = 1, 2, 3 in C and E with the d = 3 Green-width removal by the
spectral route; only true named inputs as fallbacks; decision 13: unsmoothed d = 3 successors of
L17's E3 bounds).  The frozen Lean objects and statement shapes for the item agents B, C, D and
E of the Wick-measure chain (item A's target is the existing `D1Upper.DiagramLimits`).  Nothing
in this module proves an item target.

TeX anchors: main file `notes/notes_stratonovich_ham_second_moment.tex` at revision 0788ddee
(book 1.1.0; the same line numbers at edf7085f, book 1.1.3), read with
`git show 0788ddee:notes/<file>.tex`:
* `H:homog` 384-401; the two-chain expansion 808-832 (`E:mixed-diagram` 814-824, conventions
  825-832);
* `E:pairing-source-covariance` (the capped kernel `κ_δ`, cap `δ⁻¹`, pair cap
  `(δ_j ∨ δ_h)⁻¹`, pair width `ε_j + ε_h`) 1352-1370;
* `L:damped-homogeneous-norms` 1010-1055 (the tail norms `N_1^{(M)}(1)`, `N_2^{(M)}(1)`,
  `E:damped-tail-norms` 1029-1032);
* the regularization paragraph 1643-1655 (d = 3 Green products 1652-1655);
* the section "Spatial Wick measures and fixed-order construction": setup 1657-1677
  (`J_{ε,D}`, `ρ_{ε,D}`, `ν_{ε,D}`, `ℓ_i`); `L:spatial-wick-measures` statement 1679-1694
  (`E:spatial-wick-limit` 1689-1693), proof 1696-1848: Step 1 1704-1722
  (`E:spatial-positive-laplace` 1710-1719), Steps 2-3 1726-1798 (mass bound display
  1795-1798, content 1796-1797), Step 4 1802-1820, Step 5 1824-1847 (scaling 1831-1838);
* `L:joint-fixed-order` statement 1853-1862 (joint-limit claim, first two sentences,
  1855-1858), proof 1864-1966: Step 1 1872-1888 (`F_{ε,δ,D}` 1876-1881), Step 2 1892-1927
  (`E:joint-temporal-tail` 1915-1920, "uniformly in all spatial widths" 1921, Green-smoothing
  removal 1923-1926), Step 3 1931-1945, Step 4 1949-1965 (the `L²` construction; out of scope).

Model choice M8 (the gap-coordinate Wick-measure model, decision 6).  Labels and pairings are
M4's (`DiagramModel`): `Fin (m + n)`, chain `I_1 = {i < m}`, chain `I_2 = {m ≤ i}`, the pairing
`D ∈ Pi2 m n` (a fixed-point-free involution), each pair taken once at its opener.  The gap vector
`r : Fin (m + n) → ℝ` lives on the open positive orthant; `gapTime m r` are the cumulative
times `s_l` in the own chain (inverse of M4's `incr`: `incr_gapTime`, `gapTime_incr`); `ell1`,
`ell2` are the chain lengths `ℓ_1`, `ℓ_2` (zero for an empty chain).  Spatial part with Green
**measures** exactly as M4's `spatial`: the increments `w_l ~ G_{r_l}` (`Measure.pi`), the
positions `pos m w`, and one smoothed covariance `γ_{ε_j+ε_h} = covEps Γ (ε_j + ε_h)` per pair
with **vertexwise** spatial widths `ε`.  Temporal part: per pair a Laplace domain `A_e` and the
Gamma-mixture kernel `κ_{A_e}` (`kerA`, the M7 `kappa`); vertexwise temporal widths `δ` give
`A_e = capSet (δ_j ∨ δ_h) = (0, (δ_j ∨ δ_h)⁻¹]` (and `(0,∞)` at width `0`).  Bridges:
* to M4, an **identity** at common spatial width `ε/2` per vertex and temporal width `0`:
  spatial parts `wickJ_half` (proved here), whole diagrams `M8M4IdentityTarget` (item E);
* to M7, an **inequality** for Green families with finite densities, with per-edge data
  `wickEdge` (`A_e`, `smoothSpec μ (ε_j + ε_h)`): `M8M7BridgeTarget` (item C; used by E).

Readings (for the fidelity review):
* everything is in `ℝ≥0∞`; the measures `ρ_{ε,D}`, `ν_{ε,D}` are `withDensity` measures on
  `Fin (m + n) → ℝ` supported on the open positive orthant; weak convergence of finite measures
  is convergence of the integrals of every bounded continuous real function
  (`FiniteMeasure.tendsto_iff_forall_integral_tendsto`), stated without the `FiniteMeasure`
  subtype; "all widths tend to zero at arbitrary relative rates" is the filter
  `widthFilter N = 𝓝[posOrthant N] 0` (for spatial and temporal widths jointly, its product);
* `L_{ε,D}(λ)` and the right side of `E:spatial-positive-laplace` are lower integrals of
  nonnegative functions (values in `[0,∞]`); `sup_ε L_{ε,D}(0) < ∞` is stated as one finite
  bound for all positive widths;
* `E:joint-temporal-tail` is stated subtraction-free: `F_{ε,η} ≤ F_{ε,0}`, `F_{ε,0} < ∞` and
  `F_{ε,0} ≤ F_{ε,η} + C (N_1^{(1/η)}(1) + N_2^{(1/η)}(1)²)`, with `N_2^{(M)}(1)²` the real
  `DampedNormsHomog.N2tailSq` (`N2tail = √N2tailSq`);
* the setup's "Fix `m + n = 2k ≥ 2`" is the hypothesis `m + n = 2 * k`, `1 ≤ k` of every target.

Proved here (interface sanity only): `measurableSet_capSet`, `capSet_subset_Ioi`, `capSet_zero`,
`capSet_of_pos`, `capSet_max`, `edgeWidth_mk`, `edgeMax_mk`, `edgeWidth_pos`, `capDom_mk`,
`capDom_zero`, `capDom_const`, `kerA_eq_kappa`, `kerA_Ioi`, `gapTime_eq_add_predVal`,
`incr_gapTime`, `gapTime_incr`, `pairTime_capDom_zero_incr`, `covW_half`, `wickJ_half`,
`greenS_zero`, `wickJ_greenS_zero`, `laplaceRHS_zero`, `spatialSpecW_half`, `wickL_zero`,
`wickEdge_A`, `wickEdge_μ`, `gammaOf_wickEdge`, `kappa_wickEdge`, and the named instance
`instNeBotWidthFilter`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingInterface
public import StratonovichHAMSecondMoment.PairingBridge
public import StratonovichHAMSecondMoment.DampedNormsHomog
public import StratonovichHAMSecondMoment.D1Upper

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Pointwise BoundedContinuousFunction Nat

namespace StratonovichHAMSecondMoment.WickInterface

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor smoothedGreen)
open DiagramModel (Pi2 SameChain pred predVal incr openers covEps covWeight pos spatial freq
  spatialSpec diagram diagramLim timeCov timeWeight)
open WaveGreen (waveGreen)
open WaveKernel (waveHat)
open PairingInterface

variable {d : ℕ}

/-! ### Gap coordinates, chain lengths and widths (TeX 1657-1677) -/

/-- The open positive orthant `(0,∞)^N` (gap vectors, and positive width vectors). -/
def posOrthant (N : ℕ) : Set (Fin N → ℝ) := Set.pi univ fun _ => Ioi 0

/-- "All widths tend to zero at arbitrary relative rates" (TeX 1681-1682, 1856-1857): the
filter of neighbourhoods of `0` within the positive orthant. -/
def widthFilter (N : ℕ) : Filter (Fin N → ℝ) := 𝓝[posOrthant N] 0

/-- The width filter is proper. -/
instance instNeBotWidthFilter (N : ℕ) : (widthFilter N).NeBot := by
  unfold widthFilter posOrthant
  infer_instance

/-- The cumulative time `s_l` of a gap vector: the sum of the gaps up to vertex `l` in its own
chain (TeX 1660-1662), each chain from its own root `0` (as M4's `pos`). -/
def gapTime (m : ℕ) {N : ℕ} (r : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => SameChain m j i ∧ j ≤ i), r j

/-- `ℓ_1`, the sum of the gaps in chain `I_1 = {i < m}` (TeX 1676-1677; zero for an empty
chain). -/
def ell1 (m : ℕ) {N : ℕ} (r : Fin N → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < m), r i

/-- `ℓ_2`, the sum of the gaps in chain `I_2 = {m ≤ i}` (TeX 1676-1677; zero for an empty
chain). -/
def ell2 (m : ℕ) {N : ℕ} (r : Fin N → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => m ≤ (i : ℕ)), r i

/-- The finite-horizon region `{ℓ_1 < T_1, ℓ_2 < T_2}` (TeX 1690, 1875). -/
def horizon (m : ℕ) {N : ℕ} (T1 T2 : ℝ) : Set (Fin N → ℝ) := {r | ell1 m r < T1 ∧ ell2 m r < T2}

/-- The pair spatial width `ε_j + ε_h` of an edge `{j, h}` (TeX 1669, 1358-1359). -/
def edgeWidth {α : Type*} (ε : α → ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun j h => ε j + ε h, fun _ _ => add_comm _ _⟩

/-- The pair temporal width `δ_j ∨ δ_h` of an edge `{j, h}` (TeX 1356-1357, 1879). -/
def edgeMax {α : Type*} (δ : α → ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun j h => max (δ j) (δ h), fun _ _ => max_comm _ _⟩

/-! ### The temporal kernels (TeX 1360-1370, 1876-1885) -/

/-- The Laplace domain of the capped kernel `κ_δ` (TeX 1366-1367): `(0, δ⁻¹]` for `δ > 0`
(`capSet_of_pos`) and `(0,∞)` for the full kernel `δ = 0` (`capSet_zero`). -/
def capSet (δ : ℝ) : Set ℝ := {l | 0 < l ∧ δ * l ≤ 1}

/-- The per-edge Laplace domains of vertexwise temporal widths: `A_e = capSet (δ_j ∨ δ_h)`. -/
def capDom {α : Type*} (δ : α → ℝ) : Sym2 α → Set ℝ := fun e => capSet (edgeMax δ e)

/-- The Gamma-mixture kernel on a Laplace domain `S`:
`κ_S(u) = Γ(a)⁻¹ ∫_S e^{-λ|u|} λ^{a-1} dλ` (TeX 1366-1367 with `S = (0,δ⁻¹]`; `|u|^{-a}` for
`S = (0,∞)`, `kerA_Ioi`; the tail `K_M` for `S = (M,∞)`, TeX 1023-1024).  It is M7's `kappa`
(`kerA_eq_kappa`). -/
def kerA (a : ℝ) (S : Set ℝ) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ l, ENNReal.ofReal (Real.exp (-(l * |u|))) ∂nuE a S

/-- The temporal pair product `∏_{{j,h} ∈ D} κ_{A_{jh}}(s_j - s_h)` at the cumulative times of
the gap vector `r`, each pair once at its opener (TeX 1877-1880). -/
def pairTime (a : ℝ) {N : ℕ} (A : Sym2 (Fin N) → Set ℝ) (m : ℕ) (D : Fin N → Fin N)
    (r : Fin N → ℝ) : ℝ≥0∞ :=
  ∏ i ∈ openers D, kerA a (A s(i, D i)) (gapTime m r i - gapTime m r (D i))

/-! ### The spatial Wick measures (TeX 1659-1677) -/

/-- The spatial pair product `∏_{{j,h} ∈ D} γ_{ε_j+ε_h}(y_j - y_h)` with `γ_b = p_b * Γ`
(`covEps`), each pair once at its opener (TeX 1668-1669). -/
def covW (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (D : Fin N → Fin N) (y : Fin N → Rd d) :
    ℝ≥0∞ :=
  ∏ i ∈ openers D, covEps Γ (ε i + ε (D i)) (y i - y (D i))

/-- **`J_{ε,D}(r)`** (TeX 1666-1669): `∫ ∏_l G_{r_l}(dz_l) ∏_{{j,h} ∈ D} γ_{ε_j+ε_h}(x_j - x_h)`,
the increments `z_l ~ G_{r_l}` independent (`Measure.pi`) and `x = pos m z` their cumulative sums
in the own chain; for a Green family `G` of measures (the TeX's `G` is `waveGreen d`; the d = 3
route uses `greenS 3 η`). -/
def wickJ (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) (r : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ w, covW Γ ε D (pos m w) ∂Measure.pi fun i => G (r i)

/-- **`ρ_{ε,D}(dr) = J_{ε,D}(r) dr`** on `(0,∞)^{2k}` (TeX 1670-1671). -/
def wickRho (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) : Measure (Fin N → ℝ) :=
  (volume.restrict (posOrthant N)).withDensity (wickJ G Γ ε m D)

/-- **`ν_{ε,D} = e^{-Σ_l r_l} ρ_{ε,D}`** (TeX 1675). -/
def wickNu (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) : Measure (Fin N → ℝ) :=
  (wickRho G Γ ε m D).withDensity fun r => ENNReal.ofReal (Real.exp (-∑ i, r i))

/-- **`L_{ε,D}(λ) = ∫ e^{-Σ_l λ_l r_l} dν_{ε,D}`** (TeX 1712-1713). -/
def wickL (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) (lam : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ r, ENNReal.ofReal (Real.exp (-∑ i, lam i * r i)) ∂wickNu G Γ ε m D

/-- **`ρ_D = e^{Σ_l r_l} ν_D`** for a limit `ν_D` (TeX 1683). -/
def rhoLim {N : ℕ} (ν : Measure (Fin N → ℝ)) : Measure (Fin N → ℝ) :=
  ν.withDensity fun r => ENNReal.ofReal (Real.exp (∑ i, r i))

/-- **`F_{ε,A,D}(T_1,T_2) = ∫_{ℓ_1<T_1, ℓ_2<T_2} ∏_{{j,h}} κ_{A_{jh}}(s_j - s_h) dρ_{ε,D}`**
(TeX 1876-1881), for per-edge Laplace domains `A`; the TeX's `F_{ε,δ,D}` is `A = capDom δ`
(`F_{ε,0,D}` with full factors `|s_j-s_h|^{-α₀}` is `capDom 0`, `capDom_zero`). -/
def wickF (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) (a : ℝ) {N : ℕ}
    (A : Sym2 (Fin N) → Set ℝ) (ε : Fin N → ℝ) (m : ℕ) (D : Fin N → Fin N) (T1 T2 : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ r in horizon m T1 T2, pairTime a A m D r ∂wickRho G Γ ε m D

/-- The Green-smoothed wave kernels `G_{s,η} = p_η * G_s` (`η ≥ 0`; `greenS_zero`: `η = 0` is
`waveGreen d`).  Used only by the d = 3 route (decision 8). -/
def greenS (d : ℕ) (η : ℝ) : ℝ → Measure (Rd d) := fun s => smoothedGreen (waveGreen d) s η

/-! ### The spectral forms (TeX 1704-1719) -/

/-- The spectral form of `J_{ε,D}(r)` with vertexwise widths and the Green multiplier
`e^{-η|η_l|²/2}` (`η = 0`: no multiplier; `spatialSpecW_half` relates it to M4's
`spatialSpec`): `∫ ∏_e e^{-(ε_j+ε_h)|ξ_e|²/2} ∏_l e^{-η|η_l|²/2} Ĝ_{r_l}(η_l) μ^{⊗k}(dξ)`, with
`η_l = freq m D ξ l` the coefficient of `z_l` in `Σ_e ξ_e · (x_j - x_h)` (TeX 1705-1706) and
`Ĝ_r(ξ) = sin(r|ξ|)/|ξ|` (`WaveKernel.waveHat`). -/
def spatialSpecW (μ : Measure (Rd d)) (η : ℝ) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) (r : Fin N → ℝ) : ℝ :=
  ∫ ξ, (∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)) *
      ∏ l, gaussFactor η (freq m D ξ l) * waveHat (r l) (freq m D ξ l)
    ∂Measure.pi fun _ : openers D => μ

/-- The right side of `E:spatial-positive-laplace` (TeX 1714-1717) with the Green multiplier
`e^{-η|η_l|²/2}` (`laplaceRHS_zero`: at `η = 0` it is the TeX's display):
`∫ e^{-½Σ_e(ε_j+ε_h)|ξ_e|²} ∏_l e^{-η|η_l|²/2} ((1+λ_l)² + |η_l(ξ)|²)⁻¹ ∏_e μ(dξ_e)`. -/
def laplaceRHS (μ : Measure (Rd d)) (η : ℝ) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) (lam : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ((∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)) *
      ∏ l, gaussFactor η (freq m D ξ l) / ((1 + lam l) ^ 2 + ‖freq m D ξ l‖ ^ 2))
    ∂Measure.pi fun _ : openers D => μ

/-! ### Per-edge data for the bridge to M7 -/

section Edge

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- Positive vertex widths give positive pair widths. -/
theorem edgeWidth_pos {α : Type*} {ε : α → ℝ} (hε : ∀ i, 0 < ε i) (e : Sym2 α) :
    0 < edgeWidth ε e := by
  induction e using Sym2.ind with
  | h j k => exact add_pos (hε j) (hε k)

/-- **The M7 edge datum of an M8 pair** (TeX 1905-1910: "each spatial edge measure is a finite
Gaussian-weighted `μ` with nonnegative physical covariance, and each temporal domain is a
Laplace interval or its restriction"): Laplace domain `A_e` and spectral measure
`e^{-(ε_j+ε_h)|ξ|²/2} μ(dξ)`. -/
def wickEdge (hH : HomogCovariance d alpha α₀ Γ μ) {α : Type*} {ε : α → ℝ} (hε : ∀ i, 0 < ε i)
    (A : Sym2 α → Set ℝ) (hAm : ∀ e, MeasurableSet (A e)) (hA0 : ∀ e, A e ⊆ Ioi 0)
    (e : Sym2 α) : EdgeData d where
  A := A e
  measurableSet_A := hAm e
  A_subset := hA0 e
  μ := smoothSpec μ (edgeWidth ε e)
  isFiniteMeasure_μ := PairingBridge.isFiniteMeasure_smoothSpec hH (edgeWidth_pos hε e)
  spec_nonneg := PairingBridge.specNonneg_smoothSpec hH (edgeWidth_pos hε e)

end Edge

/-! ### Frozen targets: item B (Step 1, TeX 1704-1722) -/

/-- **B target, the spectral identity of `J_{ε,D}` with vertexwise widths** (Step 1, TeX
1705-1708 at revision edf7085f (book 1.1.3): "Finite heat-weighted spectral measures and the
finite damped Green masses justify Fourier and Laplace Fubini"; with the d = 3 Green
multiplier of decision 8, `η ≥ 0`).  Under `H:homog`, at positive widths and nonnegative
gaps, `J_{ε,D}(r)` for the kernels `p_η * G` is the spectral integral.  At common width `ε/2`
and `η = 0` it is M4's `SpectralSpatial` (`spatialSpecW_half`, `wickJ_half`). -/
def SpectralSpatialWTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ η : ℝ, 0 ≤ η → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n,
    ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) → ∀ r : Fin (m + n) → ℝ, (∀ i, 0 ≤ r i) →
      wickJ (greenS d η) Γ ε m D r = ENNReal.ofReal (spatialSpecW μ η ε m D r)

/-- **B target, `E:spatial-positive-laplace`** (TeX 1710-1719 at revision edf7085f (book
1.1.3), in Step 1 1704-1722): under `H:homog`, for positive vertexwise widths and `λ_l ≥ 0`,
`L_{ε,D}(λ)` equals the spectral integral of the display. -/
def SpatialPositiveLaplaceTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n,
    ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) → ∀ lam : Fin (m + n) → ℝ, (∀ i, 0 ≤ lam i) →
      wickL (waveGreen d) Γ ε m D lam =
        ∫⁻ ξ, ENNReal.ofReal ((∏ e : openers D, gaussFactor (ε (e : Fin (m + n)) + ε (D e)) (ξ e)) *
            ∏ l, 1 / ((1 + lam l) ^ 2 + ‖freq m D ξ l‖ ^ 2))
          ∂Measure.pi fun _ : openers D => μ

/-- **B target, `E:spatial-positive-laplace` with the Green multiplier** (the route variant of
decision 8 for the d = 3 Green-width removal; TeX 1710-1719 and 1652-1655 at revision
edf7085f (book 1.1.3)): for the kernels `p_η * G`, `η ≥ 0`, the Laplace transform is
`laplaceRHS μ η`.  At `η = 0` it is `SpatialPositiveLaplaceTarget` (`greenS_zero`,
`laplaceRHS_zero`). -/
def SmoothedLaplaceTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ η : ℝ, 0 ≤ η → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n,
    ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) → ∀ lam : Fin (m + n) → ℝ, (∀ i, 0 ≤ lam i) →
      wickL (greenS d η) Γ ε m D lam = laplaceRHS μ η ε m D lam

/-- **Named input (fallback for B): `E:spatial-positive-laplace`** (TeX 1710-1719 at revision
edf7085f (book 1.1.3)).  True (it is the TeX claim); used only if B overruns. -/
structure SpatialPositiveLaplace (d : ℕ) : Prop where
  holds : SpatialPositiveLaplaceTarget d

/-! ### Frozen targets: item C (Steps 2-3 replaced, TeX 1726-1798; scaling 1831-1838) -/

/-- **C target, the uniform mass bound** (display TeX 1795-1798, content 1796-1797, at revision
edf7085f (book 1.1.3)): under `H:homog`, `sup_{ε>0} L_{ε,D}(0) < ∞`.  The TeX's explicit
right side `2^{-2k-2}(∫_0^∞ e^{-a/2} M_k(a) da)²` is specific to its Brownian route (`M_k` is
defined by Brownian occupation moments); the target is the finiteness, which route (b)
(decision 4) produces. -/
def WickMassBoundTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n,
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) →
        wickL (waveGreen d) Γ ε m D 0 ≤ C

/-- **Named input (fallback for C): the uniform mass bound** (TeX 1796-1797 at revision
edf7085f (book 1.1.3)).  True (it is the TeX claim); used only if C overruns. -/
structure WickMassBound (d : ℕ) : Prop where
  holds : WickMassBoundTarget d

/-- **C target, the scaling of `ρ_{ε,D}`** (Step 5, TeX 1831-1838 at revision edf7085f (book
1.1.3)): under `H:homog`, for Borel `A` and `c > 0`,
`ρ_{ε,D}(cA) = c^{(4-α)k} ρ_{ε/c²,D}(A)`. -/
def RhoScalingTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n,
    ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) → ∀ c : ℝ, 0 < c →
    ∀ A : Set (Fin (m + n) → ℝ), MeasurableSet A →
      wickRho (waveGreen d) Γ ε m D (c • A) =
        ENNReal.ofReal (c ^ ((4 - alpha) * k)) * wickRho (waveGreen d) Γ (fun i => ε i / c ^ 2) m D A

/-- **C target (used by E), the per-edge bridge M8 → M7** (TeX 1905-1911: the envelope applied
to the damped kernels `e^{-θs} G_s`, each spatial edge measure Gaussian-weighted, each temporal
domain a Laplace interval or its restriction): under `H:homog`, for a Green family with a
finite jointly measurable density `g` (`green1`, `green2`, `GreenSmoothed3.green3s η`), every
pairing, positive vertexwise widths, per-edge Laplace domains `A_e ⊆ (0,∞)` and damping
`θ ≥ 0`, the damped M8 integral over the whole orthant is at most the M7 diagram integral with
the per-edge data `wickEdge`.  (It is an identity; only `≤` is required.) -/
def M8M7BridgeTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    (G : ℝ → Measure (Rd d)) (g : Kernel d), Measurable (Function.uncurry g) →
    (∀ s x, g s x ≠ ⊤) → (∀ s, G s = volume.withDensity (g s)) →
    ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
    ∀ (ε : Fin (m + n) → ℝ) (hε : ∀ i, 0 < ε i) (A : Sym2 (Fin (m + n)) → Set ℝ)
      (hAm : ∀ e, MeasurableSet (A e)) (hA0 : ∀ e, A e ⊆ Ioi 0) (θ : ℝ), 0 ≤ θ →
      ∫⁻ r, ENNReal.ofReal (Real.exp (-(θ * ∑ i, r i))) * pairTime α₀ A m D r
          ∂wickRho G Γ ε m D ≤
        pairingIntegral α₀ (m4Chain m n D) (wickEdge hH hε A hAm hA0) (fun _ => damp θ g)

/-! ### Frozen targets: item D (Steps 4-5 and the lemma, TeX 1679-1694, 1802-1847) -/

/-- **Named input (fallback for D's Step 4): the weak limit** (Step 4, TeX 1802-1820 at
revision edf7085f (book 1.1.3); the first sentence of the lemma, 1680-1682): under `H:homog`,
the finite measures `ν_{ε,D}` converge weakly, as all spatial widths tend to zero at arbitrary
relative rates, to a finite measure `ν_D`. -/
def SpatialWickWeakLimitTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n,
      ∃ νD : Measure (Fin (m + n) → ℝ), IsFiniteMeasure νD ∧
        (∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) → IsFiniteMeasure (wickNu (waveGreen d) Γ ε m D)) ∧
        ∀ phi : (Fin (m + n) → ℝ) →ᵇ ℝ,
          Tendsto (fun ε => ∫ r, phi r ∂wickNu (waveGreen d) Γ ε m D) (widthFilter (m + n))
            (𝓝 (∫ r, phi r ∂νD))

/-- **Named input (fallback for D's Step 4)** (TeX 1802-1820 at revision edf7085f (book
1.1.3)).  True (it is the TeX claim); used only if D's measure-theory work overruns. -/
structure SpatialWickWeakLimit (d : ℕ) : Prop where
  holds : SpatialWickWeakLimitTarget d

/-- **D target, `L:spatial-wick-measures`, the whole lemma** (TeX 1679-1694 at revision
edf7085f (book 1.1.3), setup 1657-1677): under `H:homog`, for `m + n = 2k ≥ 2` and `D ∈ Π_k`:
the finite measures `ν_{ε,D}` converge weakly, as all spatial widths tend to zero at arbitrary
relative rates, to a finite measure `ν_D`; `ρ_D = e^{Σ r_l} ν_D` is locally finite, satisfies
`ρ_D(cA) = c^{(4-α)k} ρ_D(A)` for `c > 0`, gives zero mass to every face `r_l = 0` and every
face `ℓ_i = T > 0`; and `E:spatial-wick-limit` holds for every bounded continuous `phi` and
`T_1, T_2 > 0`. -/
def SpatialWickMeasuresTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n,
      ∃ νD : Measure (Fin (m + n) → ℝ), IsFiniteMeasure νD ∧
        (∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) → IsFiniteMeasure (wickNu (waveGreen d) Γ ε m D)) ∧
        (∀ phi : (Fin (m + n) → ℝ) →ᵇ ℝ,
          Tendsto (fun ε => ∫ r, phi r ∂wickNu (waveGreen d) Γ ε m D) (widthFilter (m + n))
            (𝓝 (∫ r, phi r ∂νD))) ∧
        IsLocallyFiniteMeasure (rhoLim νD) ∧
        (∀ c : ℝ, 0 < c → ∀ A : Set (Fin (m + n) → ℝ), MeasurableSet A →
          rhoLim νD (c • A) = ENNReal.ofReal (c ^ ((4 - alpha) * k)) * rhoLim νD A) ∧
        (∀ l : Fin (m + n), rhoLim νD {r | r l = 0} = 0) ∧
        (∀ T : ℝ, 0 < T → rhoLim νD {r | ell1 m r = T} = 0 ∧ rhoLim νD {r | ell2 m r = T} = 0) ∧
        ∀ (phi : (Fin (m + n) → ℝ) →ᵇ ℝ) (T1 T2 : ℝ), 0 < T1 → 0 < T2 →
          Tendsto (fun ε => ∫ r in horizon m T1 T2, phi r ∂wickRho (waveGreen d) Γ ε m D)
            (widthFilter (m + n)) (𝓝 (∫ r in horizon m T1 T2, phi r ∂rhoLim νD))

/-! ### Frozen targets: item E (`L:joint-fixed-order`, deterministic half, TeX 1853-1945) -/

/-- **E target, the identity M8 = M4** (TeX 814-832 with 1873-1881 and 1895-1896): under
`H:homog`, M4's diagram `J_{m,n,D}(t)` at noise width `ε` (unsmoothed Green measures, exact
time kernel) is `F_{ε',0,D}(t,t)` at the common vertex width `ε' = ε/2` (pair width
`ε/2 + ε/2 = ε`) with full temporal factors, by the change of variables `r = incr m s`. -/
def M8M4IdentityTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ ε : ℝ, 0 < ε → ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
    ∀ t : ℝ, 0 < t →
      diagram (waveGreen d) (covEps Γ ε) α₀ m n D t =
        wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) (fun _ => ε / 2) m D t t

/-- **E target, `E:joint-temporal-tail`** (TeX 1915-1921 at revision edf7085f (book 1.1.3), in
Step 2 1892-1927): under `H:homog`, for `T_1, T_2 > 0` there is a constant `C_{k,T_1,T_2}`
(depending on the fixed covariance, `D`, `k`, `T_1`, `T_2`) such that, uniformly in all
positive vertexwise spatial widths and for every common temporal width `η > 0`,
`0 ≤ F_{ε,0,D} - F_{ε,η,D} ≤ C (N_1^{(1/η)}(1) + N_2^{(1/η)}(1)²)`, with `F_{ε,0,D}` finite
(TeX 1895-1899); stated subtraction-free. -/
def JointTemporalTailTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n,
    ∀ T1 T2 : ℝ, 0 < T1 → 0 < T2 → ∃ C : ℝ, ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) →
    ∀ η : ℝ, 0 < η →
      wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 ≤
          wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ∧
        wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ≠ ⊤ ∧
        wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ≤
          wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
            ENNReal.ofReal (C * (DampedNormsHomog.N1tail α₀ η⁻¹ μ +
              DampedNormsHomog.N2tailSq α₀ η⁻¹ μ))

/-- **Named input (fallback for E): `E:joint-temporal-tail`** (TeX 1915-1921 at revision
edf7085f (book 1.1.3)).  True (it is the TeX claim); used only if E overruns. -/
structure JointTemporalTail (d : ℕ) : Prop where
  holds : JointTemporalTailTarget d

/-- **E target, the joint diagram limit of `L:joint-fixed-order`** (first two sentences, TeX
1855-1858 at revision edf7085f (book 1.1.3); proof Steps 1-3, 1872-1945): under `H:homog`,
every two-chain diagram with `m + n = 2k ≥ 2` (unequal and empty chains included) at horizon
`t > 0` has a finite joint limit as all its positive vertexwise spatial and temporal widths
tend to zero at arbitrary relative rates. -/
def JointDiagramLimitTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n, ∀ t : ℝ, 0 < t →
      ∃ b : ℝ≥0∞, b ≠ ⊤ ∧
        Tendsto (fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → ℝ) =>
            wickF (waveGreen d) Γ α₀ (capDom p.2) p.1 m D t t)
          (widthFilter (m + n) ×ˢ widthFilter (m + n)) (𝓝 b)

/-- **E target, the M4 corollary**: under `H:homog`, M4's diagrams converge as the common noise
width `ε ↓ 0` (`D1Upper.DiagramLimits`, the first clause of `MixedMoment`) and the limits are
finite (TeX 1855-1858 with 825-832). -/
def DiagramLimitsHomogTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ t : ℝ, 0 < t → D1Upper.DiagramLimits d Γ α₀ t ∧
      ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n → diagramLim d Γ α₀ m n D t ≠ ⊤

/-- **E target (decision 13), `E:homogeneous-envelope` in d = 3 for the wave Green measures**
(TeX 2352-2394 at revision edf7085f (book 1.1.3)): the successor of
`EnvelopeD3Final.homogeneous_envelope_diagrams_three_l17` with `waveGreen 3` in place of the
Green-smoothed kernels. -/
def HomogEnvelopeThreeTarget : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}, HomogCovariance 3 alpha α₀ Γ μ →
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k →
      ∀ t θ : ℝ, 0 < t → 0 < θ →
        ∑ D ∈ Pi2 m n, diagram (waveGreen 3) (covEps Γ ε) α₀ m n D t ≤
          ENNReal.ofReal ((Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
            θ ^ (-((4 - alpha - α₀) * k)))

/-- **E target (decision 13), `E:theta-envelope` in d = 3 for the wave Green measures** (TeX:
the display 2003-2006, in Step 1 1993-2031, at revision edf7085f (book 1.1.3)): the successor of
`EnvelopeD3Final.theta_envelope_diagrams_three_l17`. -/
def ThetaEnvelopeThreeTarget : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}, HomogCovariance 3 alpha α₀ Γ μ →
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t θ : ℝ), 0 < t → θ₀ ≤ θ →
      ∑ D ∈ Pi2 n n, diagram (waveGreen 3) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal ((Pi2 n n).card * Real.exp (2 * θ * t) * C ^ n * θ ^ (-(2 * (n : ℝ))))

/-- **E target (decision 13), the first inequality of `E:crude-corrected` for the diagram sums,
in d = 3 for the wave Green measures** (TeX: the display 1980-1984; its first inequality derived
in Step 2, 2036-2041; at revision edf7085f (book 1.1.3)): the successor of
`EnvelopeD3Final.crude_corrected_diagrams_three_l17`. -/
def CrudeCorrectedThreeTarget : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}, HomogCovariance 3 alpha α₀ Γ μ →
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t : ℝ), 1 ≤ n → 0 < t →
      ∑ D ∈ Pi2 n n, diagram (waveGreen 3) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ))

/-! ### Sanity lemmas (interface only) -/

section Sanity

/-- The Laplace domains are measurable. -/
theorem measurableSet_capSet (δ : ℝ) : MeasurableSet (capSet δ) :=
  (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_le (measurable_const.mul measurable_id) measurable_const)

/-- The Laplace domains lie in `(0,∞)`. -/
theorem capSet_subset_Ioi (δ : ℝ) : capSet δ ⊆ Ioi 0 := fun _ h => h.1

/-- Width `0`: the full Laplace domain `(0,∞)` (the full kernel `|u|^{-a}`). -/
theorem capSet_zero : capSet 0 = Ioi 0 := by
  ext l; simp [capSet]

/-- Width `δ > 0`: the cap `(0, δ⁻¹]` of `κ_δ` (TeX 1366-1367). -/
theorem capSet_of_pos {δ : ℝ} (hδ : 0 < δ) : capSet δ = Ioc 0 δ⁻¹ := by
  ext l
  rw [mem_Ioc, ← one_div, le_div_iff₀' hδ]
  exact Iff.rfl

/-- The pair cap is the smaller cap: `(0, (δ_j ∨ δ_h)⁻¹] = (0, δ_j⁻¹] ∩ (0, δ_h⁻¹]`
(TeX 1356-1357). -/
theorem capSet_max (a b : ℝ) : capSet (max a b) = capSet a ∩ capSet b := by
  ext l
  simp only [capSet, mem_inter_iff]
  show (0 < l ∧ max a b * l ≤ 1) ↔ (0 < l ∧ a * l ≤ 1) ∧ (0 < l ∧ b * l ≤ 1)
  constructor
  · rintro ⟨hl, h⟩
    exact ⟨⟨hl, (mul_le_mul_of_nonneg_right (le_max_left a b) hl.le).trans h⟩,
      ⟨hl, (mul_le_mul_of_nonneg_right (le_max_right a b) hl.le).trans h⟩⟩
  · rintro ⟨⟨hl, ha⟩, ⟨-, hb⟩⟩
    refine ⟨hl, ?_⟩
    rcases le_total a b with h | h
    · rw [max_eq_right h]; exact hb
    · rw [max_eq_left h]; exact ha

theorem edgeWidth_mk {α : Type*} (ε : α → ℝ) (j h : α) : edgeWidth ε s(j, h) = ε j + ε h := rfl

theorem edgeMax_mk {α : Type*} (δ : α → ℝ) (j h : α) : edgeMax δ s(j, h) = max (δ j) (δ h) := rfl

theorem capDom_mk {α : Type*} (δ : α → ℝ) (j h : α) :
    capDom δ s(j, h) = capSet (max (δ j) (δ h)) := rfl

/-- Temporal widths `0`: every edge has the full domain `(0,∞)`. -/
theorem capDom_zero {α : Type*} (e : Sym2 α) : capDom (0 : α → ℝ) e = Ioi 0 := by
  induction e using Sym2.ind with
  | h j k => simp [capDom_mk, capSet_zero]

/-- A common temporal width `η`: every edge has the domain of `κ_η`. -/
theorem capDom_const {α : Type*} (η : ℝ) (e : Sym2 α) :
    capDom (fun _ : α => η) e = capSet η := by
  induction e using Sym2.ind with
  | h j k => simp [capDom_mk]

/-- `kerA` is M7's `kappa` on the edge's Laplace domain. -/
theorem kerA_eq_kappa (a : ℝ) (E : EdgeData d) : kerA a E.A = kappa a E := rfl

/-- On `(0,∞)` the Gamma mixture is the full kernel `|u|^{-a}` (`∞` on the diagonal). -/
theorem kerA_Ioi {a : ℝ} (ha : 0 < a) (u : ℝ) : kerA a (Ioi 0) u = ENNReal.ofReal |u| ^ (-a) :=
  PairingBridge.kappa_Ioi (d := 0) ha
    ⟨Ioi 0, measurableSet_Ioi, subset_rfl, 0, inferInstance, fun _ => ⟨0, le_rfl, by simp⟩⟩
    rfl u

/-- The cumulative times satisfy `s_l = r_l + s_{p(l)}` (root value `0`). -/
theorem gapTime_eq_add_predVal (m : ℕ) {N : ℕ} (r : Fin N → ℝ) (i : Fin N) :
    gapTime m r i = r i + predVal m (gapTime m r) i := by
  rcases hp : pred m i with _ | j
  · rw [DiagramModel.predVal_of_none m _ i hp, add_zero]
    have h0 := (DiagramModel.pred_eq_none_iff m i).1 hp
    unfold gapTime
    rw [show Finset.univ.filter (fun j => SameChain m j i ∧ j ≤ i) = {i} by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        SameChain, Fin.le_def, Fin.ext_iff]
      omega]
    simp
  · rw [DiagramModel.predVal_of_some m _ i j hp]
    have hj := DiagramBridge.pred_eq_some_val m i j hp
    unfold gapTime
    rw [show Finset.univ.filter (fun l => SameChain m l i ∧ l ≤ i) =
        insert i (Finset.univ.filter fun l => SameChain m l j ∧ l ≤ j) by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        SameChain, Fin.le_def, Fin.ext_iff]
      omega]
    rw [Finset.sum_insert]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, not_and]
    intro _
    omega

/-- The increments of the cumulative times are the gaps (M4's `incr` inverts `gapTime`). -/
theorem incr_gapTime (m : ℕ) {N : ℕ} (r : Fin N → ℝ) : incr m (gapTime m r) = r := by
  funext i
  rw [incr, gapTime_eq_add_predVal m r i, add_sub_cancel_right]

/-- The cumulative times of the increments are the times. -/
theorem gapTime_incr (m : ℕ) {N : ℕ} (s : Fin N → ℝ) : gapTime m (incr m s) = s := by
  funext i
  induction' hk : (i : ℕ) using Nat.strong_induction_on with k ih generalizing i
  rw [gapTime_eq_add_predVal, incr]
  rcases hp : pred m i with _ | j
  · simp [DiagramModel.predVal_of_none m _ i hp]
  · have hj := DiagramBridge.pred_eq_some_val m i j hp
    rw [DiagramModel.predVal_of_some m _ i j hp, DiagramModel.predVal_of_some m _ i j hp,
      ih j (by omega) j rfl, sub_add_cancel]

/-- **The temporal pin to M4**: with full domains, at the increments of `s`, the pair product is
M4's `timeWeight` `∏ |s_j - s_h|^{-a}`. -/
theorem pairTime_capDom_zero_incr {a : ℝ} (ha : 0 < a) (m : ℕ) {N : ℕ} (D : Fin N → Fin N)
    (s : Fin N → ℝ) : pairTime a (capDom (0 : Fin N → ℝ)) m D (incr m s) = timeWeight a D s := by
  unfold pairTime timeWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [capDom_zero, kerA_Ioi ha, gapTime_incr, timeCov]

/-- At the common vertex width `ε/2` the pair product is M4's `covWeight` of `covEps Γ ε`. -/
theorem covW_half (Γ : Measure (Rd d)) {N : ℕ} (ε : ℝ) (D : Fin N → Fin N) (y : Fin N → Rd d) :
    covW Γ (fun _ => ε / 2) D y = covWeight (covEps Γ ε) D y := by
  unfold covW covWeight
  simp only [add_halves]

/-- **The spatial pin to M4**: at the common vertex width `ε/2`, `J_{ε,D}(r)` is M4's spatial part
with `γ_ε = covEps Γ ε` at the increments `r`. -/
theorem wickJ_half (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) {N : ℕ} (ε : ℝ) (m : ℕ)
    (D : Fin N → Fin N) (r : Fin N → ℝ) :
    wickJ G Γ (fun _ => ε / 2) m D r = spatial G (covEps Γ ε) m D r := by
  unfold wickJ spatial
  simp only [covW_half]

/-- Green width `0`: the unsmoothed wave Green measures. -/
theorem greenS_zero (d : ℕ) : greenS d 0 = waveGreen d := by
  funext s
  have := WaveGreen.isFiniteMeasure_waveGreen d s
  exact LowAlphaConvolution.smoothedGreen_zero (waveGreen d) s

/-- `J` with the Green-smoothed kernels at `η = 0` is the TeX's `J`. -/
theorem wickJ_greenS_zero (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) (r : Fin N → ℝ) :
    wickJ (greenS d 0) Γ ε m D r = wickJ (waveGreen d) Γ ε m D r := by
  rw [greenS_zero]

/-- At `η = 0` the Green multiplier is one: `laplaceRHS μ 0` is the right side of
`E:spatial-positive-laplace` (TeX 1714-1717). -/
theorem laplaceRHS_zero (μ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) (lam : Fin N → ℝ) :
    laplaceRHS μ 0 ε m D lam =
      ∫⁻ ξ, ENNReal.ofReal ((∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)) *
          ∏ l, 1 / ((1 + lam l) ^ 2 + ‖freq m D ξ l‖ ^ 2))
        ∂Measure.pi fun _ : openers D => μ := by
  unfold laplaceRHS
  simp [gaussFactor]

/-- **The spectral pin to M4**: at the common vertex width `ε/2` and `η = 0`, the spectral form
is M4's `spatialSpec μ ε` (so `SpectralSpatialWTarget` contains M4's `SpectralSpatial`). -/
theorem spatialSpecW_half (μ : Measure (Rd d)) {N : ℕ} (ε : ℝ) (m : ℕ) (D : Fin N → Fin N)
    (r : Fin N → ℝ) : spatialSpecW μ 0 (fun _ => ε / 2) m D r = spatialSpec μ ε m D r := by
  unfold spatialSpecW spatialSpec
  simp [gaussFactor, add_halves]

/-- `L_{ε,D}(0)` is the total mass of `ν_{ε,D}`. -/
theorem wickL_zero (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ)
    (m : ℕ) (D : Fin N → Fin N) : wickL G Γ ε m D 0 = wickNu G Γ ε m D univ := by
  unfold wickL
  simp

section EdgeSanity

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

theorem wickEdge_A (hH : HomogCovariance d alpha α₀ Γ μ) {α : Type*} {ε : α → ℝ}
    (hε : ∀ i, 0 < ε i) (A : Sym2 α → Set ℝ) (hAm : ∀ e, MeasurableSet (A e))
    (hA0 : ∀ e, A e ⊆ Ioi 0) (e : Sym2 α) : (wickEdge hH hε A hAm hA0 e).A = A e := rfl

theorem wickEdge_μ (hH : HomogCovariance d alpha α₀ Γ μ) {α : Type*} {ε : α → ℝ}
    (hε : ∀ i, 0 < ε i) (A : Sym2 α → Set ℝ) (hAm : ∀ e, MeasurableSet (A e))
    (hA0 : ∀ e, A e ⊆ Ioi 0) (e : Sym2 α) :
    (wickEdge hH hε A hAm hA0 e).μ = smoothSpec μ (edgeWidth ε e) := rfl

/-- The edge covariance of `wickEdge` is `γ_{ε_j+ε_h} = covEps Γ (ε_j + ε_h)`. -/
theorem gammaOf_wickEdge (hH : HomogCovariance d alpha α₀ Γ μ) {α : Type*} {ε : α → ℝ}
    (hε : ∀ i, 0 < ε i) (A : Sym2 α → Set ℝ) (hAm : ∀ e, MeasurableSet (A e))
    (hA0 : ∀ e, A e ⊆ Ioi 0) (e : Sym2 α) (x : Rd d) :
    gammaOf (wickEdge hH hε A hAm hA0 e).μ x = covEps Γ (edgeWidth ε e) x :=
  PairingBridge.gammaOf_smoothSpec hH (edgeWidth_pos hε e) x

/-- The edge time kernel of `wickEdge` is `kerA` on `A_e`. -/
theorem kappa_wickEdge (hH : HomogCovariance d alpha α₀ Γ μ) {α : Type*} {ε : α → ℝ}
    (hε : ∀ i, 0 < ε i) (A : Sym2 α → Set ℝ) (hAm : ∀ e, MeasurableSet (A e))
    (hA0 : ∀ e, A e ⊆ Ioi 0) (e : Sym2 α) (a u : ℝ) :
    kappa a (wickEdge hH hε A hAm hA0 e) u = kerA a (A e) u := rfl

end EdgeSanity

end Sanity

end StratonovichHAMSecondMoment.WickInterface
