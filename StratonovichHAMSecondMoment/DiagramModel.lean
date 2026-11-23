module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Deterministic two-chain diagram model behind `P:mixed` (a foundation; wave
L13 item DM0).  Main TeX file `notes/notes_stratonovich_ham_second_moment.tex`
at revision edf7085f:
* chaos terms `X_n = S_n(g_n(·,t,x))`, `X_0 = 1`, and `P_k = #Π_k =
  (2k)!/(2^k k!)` with its count (lines 796-804);
* the complete two-chain expansion: chains `I_1, I_2`, self- and cross-pairings
  both in `Π_k`, the predecessor `p(l)` with a separate root `(0,0)` for each
  chain, and the diagram integral `E:mixed-diagram` (lines 808-824); the
  generalized-kernel and regularization conventions (lines 825-832);
* `P:mixed` with `E:mixed-moment` and `E:full-second` (statement lines
  834-849, proof 861-927, including the chain reversal `ρ` and the pairing
  bijection `D ↦ ρ(D)` at lines 883-903);
* the source's Wick formula as quoted in `E:Sn2` (lines 542-573, Chen
  (2.19)-(2.21) and Theorem 4.1): a sum over all pair partitions of the `2n`
  points, including self-pairings, each with coefficient one;
* the total-order coefficients `A_k(t)` (lines 5446-5451) and the increment
  variables `h_l = s_l - s_{p(l)}`, `y_l` (lines 5338-5341) used by `L:d1-spatial`
  (lines 5359-5379);
* the `d = 1` Green kernel `G(s,y) = ½ 1_{|y|<s}` (lines 952, 5354), the heat
  density `p_ε` (lines 5346-5348), the joint diagram limits of
  `L:joint-fixed-order` (lines 1853-1966).

Objects (labels are 0-based: `i : Fin (m+n)` is the TeX label `i+1`; `I_1` is
`i < m`, `I_2` is `m ≤ i`):
* `pred`, `predVal`, `incr`: `p(l)` (`none` = the chain's own root, at labels
  `0` and `m`), `s_{p(l)}` with root value `0`, `h_l = s_l - s_{p(l)}`;
* `twoSimplex m n t`: `[0,t]^m_< × [0,t]^n_<` (open simplices;
  `mem_twoSimplex_iff` gives the TeX's chain inequalities);
* `Pi2 m n`: `Π_k` as `FiniteWick.pairings univ`, the fixed-point-free
  involutions of `Fin (m+n)`, self-pairings included; `openers D`: one label per
  pair (the smaller);
* `timeCov`, `timeWeight`: `∏_{(j,h) ∈ D} |s_j - s_h|^{-α₀}` in `ℝ≥0∞`;
* `covWeight γ D y = ∏_{(j,h) ∈ D} γ(y_j - y_h)` for a covariance density `γ`;
* `pos m w`: the positions `y_l` as sums of the increments `w_j` of the same
  chain up to `l`;
* `spatial G γ m D h`: the spatial integral with independent increments
  `w_l ~ G_{h_l}` (a Green family of measures) and the covariance weight at the
  positions; `diagram G γ α₀ m n D t`: `J_{m,n,D}(t)` of `E:mixed-diagram`;
* `green1`, `spatialPos`, `diagramPos`: the `d = 1` kernel and the literal
  positions form of `E:mixed-diagram` for a pointwise Green kernel;
* `covEps Γ ε = p_ε * Γ` (lower integral) and `diagramLim d Γ α₀ m n D t`, the
  limit as `ε ↓ 0` of `diagram (waveGreen d) (covEps Γ ε)`: the TeX's
  `J_{m,n,D}(t)` for a covariance measure `Γ`;
* `coeffA` (density covariance), `coeffALim` (covariance measure): `A_k(t) =
  Σ_{m=0}^{2k} Σ_{D ∈ Π_k} J_{m,2k-m,D}(t)`;
* `freq`, `spatialSpec`: the spectral form of the smoothed spatial part, with
  `Ĝ_h = WaveKernel.waveHat h` and the Gaussian factor `e^{-ε|ξ|²/2}`;
  `SpectralSpatial` states its identity with `spatial` (not proved, not used);
* `rev`, `revPairing`: the vertex involution `ρ` and `D ↦ ρ(D)`.

Readings and model choices (for the fidelity review):
* Green kernels enter as measures of the increments `y_l - y_{p(l)}`
  (`Measure.pi` of `G_{h_l}`), i.e. the increment form the TeX itself uses in
  `L:d1-spatial` ("the spatial change of variables has determinant one", line
  5341).  This is the TeX's "generalized-kernel" reading and covers the `d = 3`
  sphere measure (`WaveGreen.waveGreen 3`, the recorded `toSphere` choice).  The
  literal positions form is `diagramPos`; the change-of-variables identity
  `diagram (waveGreen 1) γ = diagramPos green1 γ` is NOT proved here (only the
  density identity `waveGreen_one_eq`).
* A covariance measure (white noise, the general `Γ` of `H:homog`) enters only
  through `covEps Γ ε` at a common noise width `ε` (the pair covariance
  `p_ε * Γ`), with the unsmoothed wave Green measures (Green smoothing removed
  first) and the exact time kernel; `diagramLim` is the `ε ↓ 0` limit.
  `L:joint-fixed-order` gives the limit at arbitrary vertexwise spatial and
  temporal widths, so this common-width spatial family has the same limit; its
  existence and finiteness are part of `MixedMoment`, and without them
  `limUnder` is unspecified.
* Each pair `{j, h}` is evaluated once, as `γ(y_j - y_h)` and `|s_j - s_h|^{-α₀}`
  with `j < h` (the TeX's pairs are unordered; for even `γ` the orientation is
  immaterial).
* The simplices are open and `|0|^{-α₀} = ∞` (`ℝ≥0∞` power); both choices
  change only null sets.
* `X n` and `u` in `MixedMoment` are arbitrary real random variables, so results
  about them are narrower by the split modelled-object rule; results stated on
  `diagram`, `diagramLim`, `coeffA`, `coeffALim` are about the model.  (When this
  module was written the solution and its chaos terms were not constructed,
  blocker D5; wave L19 constructs the chaos terms `srcX` and their series `srcU`
  on every source field and discharges `MixedMoment` for them,
  `SourceFinal.mixed_terms_l19`.)

Supplied input (named; assumed only by `mixed_moment_paper` and the
`MixedMoment.*` consequences): `MixedMoment d α₀ Γ P X u t`, the statement of
`P:mixed`: every diagram limit exists and is finite, `E[X_m X_n] = Σ_{D ∈ Π}
J_{m,n,D}(t)` with the product integrable (odd case and `m = n = 0` included),
`u²` integrable and `E u² = Σ_k A_k(t)`.  TRUE for the solution under `H:homog`
(`P:mixed`); not proved in this module.  Discharged in wave L19 for the chaos
terms `srcX` and their series `srcU` on every source field
(`SourceFinal.mixed_terms_l19`).

Formalized (all proved, nothing else supplied):
* chains and simplices: `pred_eq_none_iff`, `pred_eq_some`, `pred_second_root`
  (the second chain's own root), `sameChain_pred`, `pos_of_mem_twoSimplex`,
  `mem_twoSimplex_iff`, `incr_pos`, `measurableSet_twoSimplex`;
* pairings: `mem_Pi2`, `Pi2_odd`, `card_Pi2` (`(2k-1)!!`), `card_Pi2_mul`
  (`P_k · 2^k k! = (2k)!`, the TeX's formula), `card_openers` (`k` openers),
  the self-pairing convention `card_Pi2_two_zero`, `crossPairs_two_zero`;
* chain reversal: `rev_rev`, `sameChain_rev`, `revPairing_mem`,
  `revPairing_revPairing`, `sum_revPairing` (re-indexing a sum over `Π_k` by
  `D ↦ ρ(D)`);
* integrands: `timeCov_lt_top`, `timeCov_self`, `measurable_timeCov`,
  `measurable_timeWeight`, `timeWeight_lt_top`, `measurable_incr`,
  `measurable_pos`, `measurable_covWeight_pos`; finiteness of the spatial part
  for a bounded covariance, `spatial_le` and `spatial_waveGreen_le`
  (`≤ C^k ∏_l h_l`); `waveGreen_one_eq` (`G_s = ½ 1_{|y|<s} dy`);
* empty chains: `Pi2_zero_zero`, `diagram_zero_zero`, `diagramLim_zero_zero`,
  `coeffALim_zero` (`J_{0,0} = 1`, `A_0 = 1`);
* consequences of `MixedMoment`: `moment_odd`, `moment_zero_zero`,
  `moment_nonneg`, `coeffA_eq` (`A_k = Σ_m E[X_m X_{2k-m}]`, the TeX's
  definition), `secondMoment_eq`; wrapper `mixed_moment_paper` (hypothesis
  `H:homog` carried, unused).

Not formalized (category: foundation): the proof of `P:mixed` (D5: Wick
formula at positive widths, joint limits, `L^2` convergence of the chaos
series); the analytic identity of the terminal-chain diagram with
`J_{m,n,ρ(D)}` (only the combinatorial bijection is proved); the
positions/increments identity in `d = 1`; finiteness of `J_{m,n,D}(t)` (the
time integral of `∏ |s_j - s_h|^{-α₀}`); the spectral identity
`SpectralSpatial`; the chain-swap symmetry `J_{m,n,D} = J_{n,m,D'}`.

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.FiniteWick
public import StratonovichHAMSecondMoment.WaveGreen
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.LowAlphaConvolution

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal Nat

namespace StratonovichHAMSecondMoment.DiagramModel

open HomogHypothesis (Rd)
open WaveGreen (waveGreen waveGreen_mass)
open WaveKernel (waveHat)
open LowAlphaConvolution (heatDens gaussFactor)
open FiniteWick (pairings mem_pairings)

/-! ### Labels, chains and predecessors -/

/-- Two labels lie in the same chain: both in `I_1` or both in `I_2`.  Labels are
0-based: `i : Fin (m + n)` is the TeX label `i + 1`, so `I_1 = {1, …, m}` is
`{i : i < m}` and `I_2 = {m+1, …, m+n}` is `{i : m ≤ i}` (main TeX lines 808-809). -/
def SameChain (m : ℕ) {N : ℕ} (i j : Fin N) : Prop := ((i : ℕ) < m ↔ (j : ℕ) < m)

instance instDecidableSameChain (m : ℕ) {N : ℕ} (i j : Fin N) :
    Decidable (SameChain m i j) :=
  inferInstanceAs (Decidable (((i : ℕ) < m ↔ (j : ℕ) < m)))

/-- The preceding vertex `p(l)` in its own chain (main TeX lines 810-813):
`none` at the first vertex of either chain (label `0`, the first vertex of
`I_1`, and label `m`, the first vertex of `I_2`), which stands for the chain's
own root `(s, y) = (0, 0)`; otherwise the label just before.  So the second
chain has its own root, not the last vertex of the first chain. -/
def pred (m : ℕ) {N : ℕ} (i : Fin N) : Option (Fin N) :=
  if (i : ℕ) = 0 ∨ (i : ℕ) = m then none
  else some ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- The value of a family at the predecessor, `f_{p(l)}`, with the root value
`0` at a first vertex (`(s_{p(l)}, y_{p(l)}) = (0, 0)`, main TeX line 812). -/
def predVal (m : ℕ) {N : ℕ} {α : Type*} [Zero α] (f : Fin N → α) (i : Fin N) : α :=
  (pred m i).elim 0 f

/-- The time increments `h_l = s_l - s_{p(l)}` (main TeX lines 5338-5339). -/
def incr (m : ℕ) {N : ℕ} (s : Fin N → ℝ) (i : Fin N) : ℝ := s i - predVal m s i

/-- The two ordered time simplices `[0,t]^m_< × [0,t]^n_<` (main TeX lines 817
and 551: `[0,t]^n_< = {0 < s_1 < ⋯ < s_n < t}`), as one set of
`(m+n)`-tuples: every time exceeds its predecessor's (the root time `0` at a
first vertex) and is below `t`. -/
def twoSimplex (m n : ℕ) (t : ℝ) : Set (Fin (m + n) → ℝ) :=
  {s | ∀ i, predVal m s i < s i ∧ s i < t}

/-! ### Pairings -/

/-- `Π_k` for the two chains: all pairings of the `m + n` labels, as
`FiniteWick` fixed-point-free involutions of `Fin (m + n)`.  Self-pairings
(both endpoints in one chain) and cross-pairings are both included (main TeX
lines 809-810).  Empty for odd `m + n` (`Pi2_odd`). -/
def Pi2 (m n : ℕ) : Finset (Fin (m + n) → Fin (m + n)) :=
  pairings (Finset.univ : Finset (Fin (m + n)))

/-- The opening labels of a pairing: each pair `{j, h} ∈ D` is represented once,
by its smaller label `j < h = D j` (the TeX's orientation `(i, j)`, `i < j`, at
main TeX lines 5361-5362; the pairs of `E:mixed-diagram` are unordered). -/
def openers {N : ℕ} (D : Fin N → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => i < D i

/-- The cross-pairings: every pair has one endpoint in each chain.  Not the
TeX's `Π_k` (which also has the self-pairings); used only to pin the
self-pairing convention. -/
def crossPairs (m n : ℕ) : Finset (Fin (m + n) → Fin (m + n)) :=
  (Pi2 m n).filter fun D => ∀ i, ¬ SameChain m i (D i)

/-! ### The integrands -/

/-- The temporal covariance `|a - b|^{-α₀}` of `E:cov` (main TeX line 379), in
`ℝ≥0∞` (so `|0|^{-α₀} = ∞` for `α₀ > 0`, not Lean's real junk value `0`). -/
def timeCov (α₀ a b : ℝ) : ℝ≥0∞ := (ENNReal.ofReal |a - b|) ^ (-α₀)

/-- The temporal pairing weight `∏_{(j,h) ∈ D} |s_j - s_h|^{-α₀}` (main TeX
line 822). -/
def timeWeight {N : ℕ} (α₀ : ℝ) (D : Fin N → Fin N) (s : Fin N → ℝ) : ℝ≥0∞ :=
  ∏ i ∈ openers D, timeCov α₀ (s i) (s (D i))

/-- The spatial pairing weight `∏_{(j,h) ∈ D} γ(y_j - y_h)` (main TeX line 822),
for a covariance density `γ`, at the positions `y`; each pair is taken once, at
its opener `j < h` (for the even covariances of `H:homog` the orientation does
not matter). -/
def covWeight {d N : ℕ} (γ : Rd d → ℝ≥0∞) (D : Fin N → Fin N) (y : Fin N → Rd d) : ℝ≥0∞ :=
  ∏ i ∈ openers D, γ (y i - y (D i))

/-- The positions from the spatial increments `w`: `y_l = Σ_{j ≤ l, j in the
chain of l} w_j`, each chain started at its own root `0` (main TeX lines
5339-5341: "`x_l` is the sum of increments in its own chain up to label `l`"). -/
def pos (m : ℕ) {d N : ℕ} (w : Fin N → Rd d) (i : Fin N) : Rd d :=
  ∑ j ∈ Finset.univ.filter (fun j => SameChain m j i ∧ j ≤ i), w j

/-- The spatial part of a diagram at time increments `h`, for a Green family `G`
of measures: the increments `w_l` are independent with laws `G_{h_l}`, and the
covariance weight is evaluated at the positions `y = pos w`.  This is the
`dy`-integral of `E:mixed-diagram` with `G(h_l, y_l - y_{p(l)}) dy_l` read as
the measure `G_{h_l}` of the increment `y_l - y_{p(l)}` (the TeX's
generalized-kernel reading, main TeX lines 825-829, needed for the `d = 3`
sphere measure), and in increment variables as in `S_{D,ε}(h)` of main TeX lines
5351-5356.  For a Green kernel with a density, `spatialPos` is the literal
positions form. -/
def spatial {d : ℕ} (G : ℝ → Measure (Rd d)) (γ : Rd d → ℝ≥0∞) (m : ℕ) {N : ℕ}
    (D : Fin N → Fin N) (h : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ w, covWeight γ D (pos m w) ∂(Measure.pi fun i => G (h i))

/-- The diagram integral `J_{m,n,D}(t)` of `E:mixed-diagram` (main TeX lines
814-824) for a Green family `G` and a covariance density `γ`: the
`ds`-integral over `[0,t]^m_< × [0,t]^n_<` of the temporal weight times the
spatial part at the increments `h_l = s_l - s_{p(l)}`.  The model's `G` is
`waveGreen d`; for a covariance measure `Γ` the TeX's `J` is the limit
`diagramLim` of the smoothed `γ_ε = covEps Γ ε`. -/
def diagram {d : ℕ} (G : ℝ → Measure (Rd d)) (γ : Rd d → ℝ≥0∞) (α₀ : ℝ) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s * spatial G γ m D (incr m s)

/-- The `d = 1` wave Green kernel `G(s, y) = ½ 1_{|y| < s}` (main TeX lines 952
and 5354), pointwise. -/
def green1 (s : ℝ) (y : Rd 1) : ℝ≥0∞ :=
  (Metric.ball (0 : Rd 1) s).indicator (fun _ => ENNReal.ofReal (1 / 2)) y

/-- The literal positions form of the spatial integral of `E:mixed-diagram` for
a Green kernel `g` with values `g(h, z)`:
`∫ ∏_l g(h_l, y_l - y_{p(l)}) ∏_{(j,h) ∈ D} γ(y_j - y_h) dy` (main TeX lines
818-822). -/
def spatialPos {d : ℕ} (g : ℝ → Rd d → ℝ≥0∞) (γ : Rd d → ℝ≥0∞) (m : ℕ) {N : ℕ}
    (D : Fin N → Fin N) (h : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, (∏ i, g (h i) (y i - predVal m y i)) * covWeight γ D y

/-- The literal positions form of `E:mixed-diagram` for a pointwise Green
kernel `g` (in `d = 1`, `g = green1`). -/
def diagramPos {d : ℕ} (g : ℝ → Rd d → ℝ≥0∞) (γ : Rd d → ℝ≥0∞) (α₀ : ℝ) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s * spatialPos g γ m D (incr m s)

/-- The smoothed covariance `γ_ε = p_ε * Γ`, `γ_ε(x) = ∫ p_ε(x - z) Γ(dz)`, with
`p_ε` the centered Gaussian density of covariance `ε I`
(`LowAlphaConvolution.heatDens`; main TeX lines 5346-5348), as a lower
Lebesgue integral (never a junk value). -/
def covEps {d : ℕ} (Γ : Measure (Rd d)) (ε : ℝ) (x : Rd d) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (heatDens ε (x - z)) ∂Γ

/-- The TeX's `J_{m,n,D}(t)` for a covariance measure `Γ` (white noise, `d = 3`
and the general covariance of `H:homog`): the limit, as the spatial noise width
`ε ↓ 0`, of the diagrams with the smoothed covariance `γ_ε` and the unsmoothed
wave Green measures (main TeX lines 825-832: "the generalized-kernel and
regularization conventions"; Green smoothing removed before noise smoothing,
lines 1860-1861).  The limit exists by `L:joint-fixed-order` (lines
1853-1966); this existence is part of the supplied input `MixedMoment`, and
without it `limUnder` is an unspecified value. -/
def diagramLim (d : ℕ) (Γ : Measure (Rd d)) (α₀ : ℝ) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) (t : ℝ) : ℝ≥0∞ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => diagram (waveGreen d) (covEps Γ ε) α₀ m n D t

/-- The total-order coefficient `A_k(t) = Σ_{m=0}^{2k} Σ_{D ∈ Π_k}
J_{m,2k-m,D}(t)` for a Green family and a covariance density (the diagram side
of main TeX lines 5446-5451 and of `E:full-second`, lines 844-847). -/
def coeffA {d : ℕ} (G : ℝ → Measure (Rd d)) (γ : Rd d → ℝ≥0∞) (α₀ : ℝ) (k : ℕ) (t : ℝ) :
    ℝ≥0∞ :=
  ∑ m ∈ Finset.range (2 * k + 1), ∑ D ∈ Pi2 m (2 * k - m), diagram G γ α₀ m (2 * k - m) D t

/-- `A_k(t)` for a covariance measure `Γ` in dimension `d`: the same sum of the
limits `diagramLim`.  By `MixedMoment.coeffA_eq` it equals the TeX's
definition `Σ_{m=0}^{2k} E[X_m X_{2k-m}]` (main TeX line 5448). -/
def coeffALim (d : ℕ) (Γ : Measure (Rd d)) (α₀ : ℝ) (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∑ m ∈ Finset.range (2 * k + 1), ∑ D ∈ Pi2 m (2 * k - m), diagramLim d Γ α₀ m (2 * k - m) D t

/-! ### The spectral form -/

/-- The frequency carried by the increment at label `l` in the spectral form:
with one frequency `ξ_e` per pair `e = (j, h)`, `j < h`,
`η_l = Σ_e ξ_e (1[l ≤ j, same chain] - 1[l ≤ h, same chain])`, because
`Σ_e ξ_e · (y_j - y_h) = Σ_l η_l · w_l` when `y = pos w` (the sum over the pairs `e`). -/
def freq (m : ℕ) {d N : ℕ} (D : Fin N → Fin N) (ξ : openers D → Rd d) (l : Fin N) : Rd d :=
  ∑ e : openers D,
    ((if SameChain m l (e : Fin N) ∧ l ≤ (e : Fin N) then (1 : ℝ) else 0) -
      (if SameChain m l (D e) ∧ l ≤ D e then (1 : ℝ) else 0)) • ξ e

/-- The spectral form of the spatial part at noise width `ε` for a covariance
with spectral measure `μ` (`Γ = ∫ e^{iξ·x} μ(dξ)`, `H:homog`):
`∫ ∏_e e^{-ε|ξ_e|²/2} ∏_l Ĝ_{h_l}(η_l) μ^{⊗k}(dξ)`, with
`Ĝ_h(ξ) = sin(h|ξ|)/|ξ|` (`WaveKernel.waveHat`).  Its identity with
`spatial (waveGreen d) (covEps Γ ε)` is the statement `SpectralSpatial`, not
proved here (proved in wave L18: `WickSpectral.spectralSpatial_homog`).  At
`ε = 0` the integrand need not be absolutely integrable (for white noise a
self-pair at adjacent labels gives `∫ |sin(h|ξ|)/|ξ|| dξ = ∞`), so zero-width
integrability is not guaranteed and the general results are stated for `ε > 0`. -/
def spatialSpec {d : ℕ} (μ : Measure (Rd d)) (ε : ℝ) (m : ℕ) {N : ℕ} (D : Fin N → Fin N)
    (h : Fin N → ℝ) : ℝ :=
  ∫ ξ, (∏ e, gaussFactor ε (ξ e)) * ∏ l, waveHat (h l) (freq m D ξ l)
    ∂(Measure.pi fun _ : openers D => μ)

/-- The spectral identity of the smoothed spatial part (a TRUE statement for
`Γ`, `μ` as in `H:homog`, `ε > 0`, `h ≥ 0`, `d ∈ {1,2,3}`, by
`γ_ε(x) = ∫ e^{iξ·x} e^{-ε|ξ|²/2} μ(dξ)` (`LowAlphaConvolution.gammaEps_spectral`),
Fubini and `∫ e^{iη·w} G_h(dw) = Ĝ_h(η)`).  Recorded for the later items that
use the spectral form; no theorem of this module assumes it.  Proved in wave L18 under
`H:homog`: `WickSpectral.spectralSpatial_homog`. -/
def SpectralSpatial (d : ℕ) (Γ μ : Measure (Rd d)) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (m : ℕ) {N : ℕ} (D : Fin N → Fin N), D ∈ pairings Finset.univ →
    ∀ h : Fin N → ℝ, (∀ i, 0 ≤ h i) →
      spatial (waveGreen d) (covEps Γ ε) m D h = ENNReal.ofReal (spatialSpec μ ε m D h)

/-! ### The supplied input `MixedMoment` -/

/-- **Supplied input `MixedMoment`** (`P:mixed`, main TeX lines 834-849, with
`E:mixed-moment` and `E:full-second`; blocker D5 when this module was written,
the Stratonovich chaos expansion of the solution).  For random variables `X n` (the chaos terms
`X_n(t,x) = S_n(g_n(·,t,x))`, main TeX line 796) and `u` (the solution
`u(t,x)`) on `(Ω, P)`, for the covariance `|s - r|^{-α₀} Γ` in dimension `d`:
1. every diagram has a finite limit as the noise width tends to zero (part of
   `L:joint-fixed-order`), so `diagramLim` is the TeX's `J_{m,n,D}(t)`;
2. `E[X_m X_n] = Σ_{D ∈ Π} J_{m,n,D}(t)` with the product integrable
   (`E:mixed-moment`; for odd `m + n` the sum is empty, so the moment is `0`,
   and for `m = n = 0` it is `1`: `MixedMoment.moment_odd`,
   `MixedMoment.moment_zero_zero`);
3. `u²` is integrable and `E u² = Σ_k A_k(t)` with
   `A_k(t) = Σ_{m=0}^{2k} Σ_D J_{m,2k-m,D}(t)` (`E:full-second`), a convergent
   series of nonnegative terms.
TRUE for the solution of the model under `H:homog` (`P:mixed`); assumed here.
Discharged in wave L19 for the chaos terms `srcX` and their series `srcU` on
every source field under `H:homog`, for `t > 0` and every `x` (model M9):
`SourceFinal.mixed_terms_l19`
(`SourceFinal.mixedMoment_m9_l19` at the constructed `m9`). -/
def MixedMoment (d : ℕ) (α₀ : ℝ) (Γ : Measure (Rd d)) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (u : Ω → ℝ) (t : ℝ) : Prop :=
  (∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
      Tendsto (fun ε => diagram (waveGreen d) (covEps Γ ε) α₀ m n D t) (𝓝[>] 0)
          (𝓝 (diagramLim d Γ α₀ m n D t)) ∧
        diagramLim d Γ α₀ m n D t ≠ ⊤) ∧
    (∀ m n : ℕ, Integrable (fun ω => X m ω * X n ω) P ∧
      ∫ ω, X m ω * X n ω ∂P = ∑ D ∈ Pi2 m n, (diagramLim d Γ α₀ m n D t).toReal) ∧
    Integrable (fun ω => u ω ^ 2) P ∧
    HasSum (fun k => (coeffALim d Γ α₀ k t).toReal) (∫ ω, u ω ^ 2 ∂P)


/-! ### Chains and the time simplices -/

/-- The first vertex of either chain has no predecessor (the root): labels `0` and
`m`. -/
theorem pred_eq_none_iff (m : ℕ) {N : ℕ} (i : Fin N) :
    pred m i = none ↔ (i : ℕ) = 0 ∨ (i : ℕ) = m := by
  unfold pred; split_ifs with h <;> simp [h]

/-- Away from the two first vertices the predecessor is the label just before. -/
theorem pred_eq_some (m : ℕ) {N : ℕ} (i : Fin N) (h0 : (i : ℕ) ≠ 0) (hm : (i : ℕ) ≠ m) :
    pred m i = some ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ := by
  unfold pred
  simp only [show ¬((i : ℕ) = 0 ∨ (i : ℕ) = m) by omega, ite_false]

/-- The second chain has its own root: its first label `m` has no predecessor
(main TeX lines 812-813). -/
theorem pred_second_root (m n : ℕ) (hn : 0 < n) :
    pred m (⟨m, by omega⟩ : Fin (m + n)) = none :=
  (pred_eq_none_iff m _).2 (Or.inr rfl)

/-- A predecessor is in the same chain as its label. -/
theorem sameChain_pred (m : ℕ) {N : ℕ} (i j : Fin N) (h : pred m i = some j) :
    SameChain m j i := by
  unfold pred at h
  split_ifs at h with h0
  cases h
  unfold SameChain
  simp only
  omega

/-- The predecessor value at a first vertex is the root value `0`. -/
theorem predVal_of_none (m : ℕ) {N : ℕ} {α : Type*} [Zero α] (f : Fin N → α) (i : Fin N)
    (h : pred m i = none) : predVal m f i = 0 := by
  simp [predVal, h]

/-- The predecessor value at any other vertex is the value at the predecessor. -/
theorem predVal_of_some (m : ℕ) {N : ℕ} {α : Type*} [Zero α] (f : Fin N → α) (i j : Fin N)
    (h : pred m i = some j) : predVal m f i = f j := by
  simp [predVal, h]

/-- In the time simplices every time is positive. -/
theorem pos_of_mem_twoSimplex {m n : ℕ} {t : ℝ} {s : Fin (m + n) → ℝ}
    (hs : s ∈ twoSimplex m n t) (i : Fin (m + n)) : 0 < s i := by
  induction' hk : (i : ℕ) using Nat.strong_induction_on with k ih generalizing i
  have h := (hs i).1
  rcases hp : pred m i with _ | j
  · rwa [predVal_of_none m s i hp] at h
  · rw [predVal_of_some m s i j hp] at h
    have hj : (j : ℕ) < k := by
      unfold pred at hp; split_ifs at hp with h0; cases hp; simp only; omega
    exact lt_trans (ih _ hj j rfl) h

/-- The time simplices are exactly `[0,t]^m_< × [0,t]^n_<` (main TeX lines 817,
551): all times lie in `(0, t)`, and consecutive labels of one chain (a label
`j = i + 1` that is not the first label `m` of the second chain) are strictly
increasing. -/
theorem mem_twoSimplex_iff {m n : ℕ} {t : ℝ} (s : Fin (m + n) → ℝ) :
    s ∈ twoSimplex m n t ↔ (∀ i, 0 < s i ∧ s i < t) ∧
      ∀ i j : Fin (m + n), (j : ℕ) = i + 1 → (j : ℕ) ≠ m → s i < s j := by
  constructor
  · intro hs
    refine ⟨fun i => ⟨pos_of_mem_twoSimplex hs i, (hs i).2⟩, fun i j hij hjm => ?_⟩
    have hp := pred_eq_some m j (by omega) hjm
    have h := (hs j).1
    rw [predVal_of_some m s j _ hp] at h
    have : (⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ : Fin (m + n)) = i := by
      ext; simp only; omega
    rwa [this] at h
  · rintro ⟨hpos, hinc⟩ i
    refine ⟨?_, (hpos i).2⟩
    rcases hp : pred m i with _ | j
    · rw [predVal_of_none m s i hp]; exact (hpos i).1
    · rw [predVal_of_some m s i j hp]
      unfold pred at hp; split_ifs at hp with h0; cases hp
      exact hinc _ i (by simp only; omega) (by omega)

/-- In the time simplices every time increment `h_l = s_l - s_{p(l)}` is positive. -/
theorem incr_pos {m n : ℕ} {t : ℝ} {s : Fin (m + n) → ℝ} (hs : s ∈ twoSimplex m n t)
    (i : Fin (m + n)) : 0 < incr m s i :=
  sub_pos.2 (hs i).1

/-- The time simplices are measurable. -/
theorem measurableSet_twoSimplex (m n : ℕ) (t : ℝ) : MeasurableSet (twoSimplex m n t) := by
  have : twoSimplex m n t = ⋂ i, ({s | predVal m s i < s i} ∩ {s | s i < t}) := by
    ext s; simp [twoSimplex]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.inter ?_ ?_
  · rcases hp : pred m i with _ | j
    · simp_rw [predVal_of_none m _ i hp]
      exact measurableSet_lt measurable_const (measurable_pi_apply i)
    · simp_rw [predVal_of_some m _ i j hp]
      exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  · exact measurableSet_lt (measurable_pi_apply i) measurable_const

/-! ### Pairings: count, openers, self-pairings -/

/-- Membership in `Π`: a fixed-point-free involution of the labels. -/
theorem mem_Pi2 {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} :
    D ∈ Pi2 m n ↔ ∀ i, D i ≠ i ∧ D (D i) = i := by
  simp [Pi2, mem_pairings]

/-- There is no pairing of an odd number of labels: `E:mixed-moment`'s odd case. -/
theorem Pi2_odd {m n : ℕ} (h : Odd (m + n)) : Pi2 m n = ∅ := by
  obtain ⟨k, hk⟩ := h
  exact FiniteWick.card_pairings_odd k _ (by simp [hk])

/-- `#Π_k = (2k-1)!!` for `m + n = 2k`. -/
theorem card_Pi2 {m n k : ℕ} (hk : m + n = 2 * k) : (Pi2 m n).card = (2 * k - 1)‼ :=
  FiniteWick.card_pairings_even k _ (by simp [hk])

/-- The TeX's count `P_k = #Π_k = (2k)!/(2^k k!)` (main TeX line 799), in the
division-free form `P_k · 2^k k! = (2k)!`. -/
theorem card_Pi2_mul {m n k : ℕ} (hk : m + n = 2 * k) :
    (Pi2 m n).card * (2 ^ k * k !) = (2 * k)! := by
  rw [card_Pi2 hk, ← Nat.doubleFactorial_two_mul]
  rcases k with _ | k
  · simp
  · have h := Nat.factorial_eq_mul_doubleFactorial (2 * (k + 1) - 1)
    rw [show 2 * (k + 1) - 1 + 1 = 2 * (k + 1) by omega] at h
    rw [h, mul_comm]

/-- Exactly half of the labels open a pair: a pairing of `2k` labels has `k`
openers (and `k` closers). -/
theorem card_openers {N k : ℕ} {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) (hN : N = 2 * k) :
    (openers D).card = k := by
  rw [mem_pairings] at hD
  have hinv : ∀ i, D (D i) = i := fun i => (hD.1 i (Finset.mem_univ _)).2.2
  have hne : ∀ i, D i ≠ i := fun i => (hD.1 i (Finset.mem_univ _)).2.1
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun i => i < D i)
  have hC : (Finset.univ.filter fun i : Fin N => ¬ i < D i).card = (openers D).card := by
    refine Finset.card_nbij' D D ?_ ?_ ?_ ?_
    · intro i hi
      have hi' : ¬ i < D i := (Finset.mem_filter.1 hi).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [hinv]
      exact lt_of_le_of_ne (not_lt.1 hi') (hne i)
    · intro i hi
      have hi' : i < D i := (Finset.mem_filter.1 hi).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [hinv]
      exact not_lt.2 hi'.le
    · intro i _; exact hinv i
    · intro i _; exact hinv i
  rw [Finset.card_univ, Fintype.card_fin, hC] at hsplit
  change (openers D).card + (openers D).card = N at hsplit
  omega

/-- The self-pairing convention (main TeX lines 809-810): a pairing of two labels
of the first chain is in `Π_1`.  With `m = 2`, `n = 0` the only pairing is this
self-pairing, which is not a cross-pairing. -/
theorem card_Pi2_two_zero : (Pi2 2 0).card = 1 := by
  rw [card_Pi2 (m := 2) (n := 0) (k := 1) rfl]; rfl

/-- With `m = 2`, `n = 0` there is no cross-pairing. -/
theorem crossPairs_two_zero : crossPairs 2 0 = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun D _ h => ?_
  have := h 0
  apply this
  unfold SameChain
  have := (D 0).isLt
  simp only [Fin.val_zero]
  omega

/-! ### Chain reversal (the vertex involution `ρ`) -/

/-- The vertex involution `ρ` of the proof of `P:mixed` (main TeX lines 897-900):
`ρ(j) = m + 1 - j` on `I_1` and `ρ(m + j) = m + n + 1 - j` on `I_2` (1-based);
0-based, `i ↦ m - 1 - i` for `i < m` and `i ↦ 2m + n - 1 - i` otherwise.  It
reverses each chain, turning the terminal chains of `E:expansion` into initial
chains rooted at `(0, 0)`. -/
def rev (m n : ℕ) (i : Fin (m + n)) : Fin (m + n) :=
  if h : (i : ℕ) < m then ⟨m - 1 - i, by omega⟩ else ⟨2 * m + n - 1 - i, by omega⟩

/-- `ρ` is an involution. -/
theorem rev_rev (m n : ℕ) (i : Fin (m + n)) : rev m n (rev m n i) = i := by
  have := i.isLt
  unfold rev
  split_ifs with h1 h2 h2 <;> (ext; simp only at h1 h2 ⊢; omega)

/-- `ρ` maps each chain to itself. -/
theorem sameChain_rev (m n : ℕ) (i : Fin (m + n)) : SameChain m (rev m n i) i := by
  have := i.isLt
  unfold rev SameChain
  split_ifs with h <;> simp only <;> omega

/-- The pairing bijection `D ↦ {{ρ(a), ρ(b)} : {a,b} ∈ D}` (main TeX lines
902-903): as an involution, `ρ ∘ D ∘ ρ`. -/
def revPairing (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) : Fin (m + n) → Fin (m + n) :=
  rev m n ∘ D ∘ rev m n

/-- `ρ(D)` is again a pairing. -/
theorem revPairing_mem {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) :
    revPairing m n D ∈ Pi2 m n := by
  rw [mem_Pi2] at hD ⊢
  intro i
  refine ⟨fun h => (hD (rev m n i)).1 ?_, ?_⟩
  · have := congrArg (rev m n) h
    simpa [revPairing, rev_rev] using this
  · simp [revPairing, rev_rev, (hD _).2]

/-- `D ↦ ρ(D)` is an involution. -/
theorem revPairing_revPairing (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) :
    revPairing m n (revPairing m n D) = D := by
  funext i; simp [revPairing, rev_rev]

/-- `D ↦ ρ(D)` is a bijection of `Π_k`, so a sum over `Π_k` may be re-indexed by
it (the re-indexing in the proof of `P:mixed`, main TeX lines 900-903). -/
theorem sum_revPairing {m n : ℕ} {β : Type*} [AddCommMonoid β]
    (f : (Fin (m + n) → Fin (m + n)) → β) :
    ∑ D ∈ Pi2 m n, f (revPairing m n D) = ∑ D ∈ Pi2 m n, f D :=
  Finset.sum_nbij' (revPairing m n) (revPairing m n) (fun _ h => revPairing_mem h)
    (fun _ h => revPairing_mem h) (fun D _ => revPairing_revPairing m n D)
    (fun D _ => revPairing_revPairing m n D) (fun _ _ => rfl)

/-! ### The integrands: measurability and finiteness -/

/-- At distinct times the temporal covariance is finite. -/
theorem timeCov_lt_top (α₀ : ℝ) {a b : ℝ} (hab : a ≠ b) : timeCov α₀ a b < ⊤ := by
  unfold timeCov
  refine lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_ne_zero ?_ ENNReal.ofReal_ne_top)
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact abs_pos.2 (sub_ne_zero.2 hab)

/-- At equal times the temporal covariance is `∞` (for `α₀ > 0`). -/
theorem timeCov_self {α₀ : ℝ} (hα : 0 < α₀) (a : ℝ) : timeCov α₀ a a = ⊤ := by
  simp [timeCov, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hα)]

/-- The temporal covariance is jointly measurable. -/
theorem measurable_timeCov (α₀ : ℝ) :
    Measurable fun p : ℝ × ℝ => timeCov α₀ p.1 p.2 := by
  unfold timeCov
  exact (ENNReal.measurable_ofReal.comp (measurable_fst.sub measurable_snd).abs).pow_const _

/-- The temporal pairing weight is measurable in the times. -/
theorem measurable_timeWeight {N : ℕ} (α₀ : ℝ) (D : Fin N → Fin N) :
    Measurable (timeWeight α₀ D) := by
  unfold timeWeight
  refine Finset.measurable_prod _ fun i _ => ?_
  have hg : Measurable fun s : Fin N → ℝ => (s i, s (D i)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply (D i))
  exact (measurable_timeCov α₀).comp hg

/-- The temporal weight is finite when the paired times are distinct (off a
Lebesgue-null set of times). -/
theorem timeWeight_lt_top {N : ℕ} (α₀ : ℝ) (D : Fin N → Fin N) (s : Fin N → ℝ)
    (hs : ∀ i, s i ≠ s (D i) ∨ D i = i) (hD : ∀ i, D i ≠ i) : timeWeight α₀ D s < ⊤ := by
  unfold timeWeight
  refine ENNReal.prod_lt_top fun i _ => timeCov_lt_top α₀ ?_
  rcases hs i with h | h
  · exact h
  · exact absurd h (hD i)

/-- The time increments are measurable. -/
theorem measurable_incr (m : ℕ) {N : ℕ} : Measurable (incr m (N := N)) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold incr
  rcases hp : pred m i with _ | j
  · simp_rw [predVal_of_none m _ i hp]; exact (measurable_pi_apply i).sub measurable_const
  · simp_rw [predVal_of_some m _ i j hp]
    exact (measurable_pi_apply i).sub (measurable_pi_apply j)

/-- The positions are measurable functions of the increments. -/
theorem measurable_pos (m : ℕ) {d N : ℕ} (i : Fin N) :
    Measurable fun w : Fin N → Rd d => pos m w i :=
  Finset.measurable_sum _ fun j _ => measurable_pi_apply j

/-- The spatial integrand of `spatial` is measurable for a measurable covariance. -/
theorem measurable_covWeight_pos (m : ℕ) {d N : ℕ} {γ : Rd d → ℝ≥0∞} (hγ : Measurable γ)
    (D : Fin N → Fin N) : Measurable fun w : Fin N → Rd d => covWeight γ D (pos m w) := by
  unfold covWeight
  exact Finset.measurable_prod _ fun i _ =>
    hγ.comp ((measurable_pos m i).sub (measurable_pos m (D i)))

/-- A bounded covariance gives a finite spatial part:
`spatial ≤ C^k ∏_l G_{h_l}(ℝ^d)` with `k` the number of pairs. -/
theorem spatial_le {d : ℕ} (G : ℝ → Measure (Rd d)) [∀ s, SigmaFinite (G s)]
    {γ : Rd d → ℝ≥0∞} {C : ℝ≥0∞} (hγ : ∀ x, γ x ≤ C) (m : ℕ) {N : ℕ} (D : Fin N → Fin N)
    (h : Fin N → ℝ) :
    spatial G γ m D h ≤ C ^ (openers D).card * ∏ i, G (h i) Set.univ := by
  unfold spatial
  calc ∫⁻ w, covWeight γ D (pos m w) ∂(Measure.pi fun i => G (h i))
      ≤ ∫⁻ _, C ^ (openers D).card ∂(Measure.pi fun i => G (h i)) :=
        lintegral_mono fun w => Finset.prod_le_pow_card _ _ _ fun i _ => hγ _
    _ = _ := by rw [lintegral_const, Measure.pi_univ]

/-- For the wave Green measures (`d ∈ {1,2,3}`, masses `G_h(ℝ^d) = h`), a
covariance bounded by `C` gives `spatial ≤ C^k ∏_l h_l`. -/
theorem spatial_waveGreen_le {d : ℕ} (hd : d = 1 ∨ d = 2 ∨ d = 3) {γ : Rd d → ℝ≥0∞}
    {C : ℝ≥0∞} (hγ : ∀ x, γ x ≤ C) (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ)
    (hh : ∀ i, 0 ≤ h i) :
    spatial (waveGreen d) γ m D h ≤ C ^ (openers D).card * ∏ i, ENNReal.ofReal (h i) := by
  refine (spatial_le _ hγ m D h).trans (le_of_eq ?_)
  congr 1
  exact Finset.prod_congr rfl fun i _ => waveGreen_mass d hd _ (hh i)

/-- The `d = 1` wave Green measure has the density `green1`:
`G_s(dy) = ½ 1_{|y|<s} dy`. -/
theorem waveGreen_one_eq (s : ℝ) : waveGreen 1 s = volume.withDensity (green1 s) := by
  rw [show green1 s = (Metric.ball (0 : Rd 1) s).indicator (fun _ => ENNReal.ofReal (1 / 2))
    from rfl, withDensity_indicator Metric.isOpen_ball.measurableSet, withDensity_const]
  rfl

/-! ### The empty diagram -/

/-- Two empty chains have exactly one pairing, the empty one. -/
theorem Pi2_zero_zero : Pi2 0 0 = {id} := by
  have : IsEmpty (Fin (0 + 0)) := inferInstanceAs (IsEmpty (Fin 0))
  have : (Finset.univ : Finset (Fin (0 + 0))) = ∅ := Finset.univ_eq_empty
  rw [Pi2, this, FiniteWick.pairings_empty]

/-- Two empty chains contribute the factor one (main TeX lines 825 and 843:
"the case `m = n = 0` equals one"). -/
theorem diagram_zero_zero {d : ℕ} (G : ℝ → Measure (Rd d)) (γ : Rd d → ℝ≥0∞) (α₀ : ℝ)
    (D : Fin (0 + 0) → Fin (0 + 0)) (t : ℝ) : diagram G γ α₀ 0 0 D t = 1 := by
  have : IsEmpty (Fin (0 + 0)) := inferInstanceAs (IsEmpty (Fin 0))
  have hset : twoSimplex 0 0 t = Set.univ := by
    ext s
    exact iff_of_true (fun i => i.elim0) (Set.mem_univ _)
  have hone : ∀ s, timeWeight α₀ D s * spatial G γ 0 D (incr 0 s) = 1 := by
    intro s
    have ho : openers D = ∅ := Finset.eq_empty_of_isEmpty _
    simp only [timeWeight, spatial, covWeight, ho, Finset.prod_empty, one_mul]
    rw [Measure.pi_of_empty (x := fun i => i.elim0), lintegral_const, measure_univ, one_mul]
  unfold diagram
  rw [hset, Measure.restrict_univ]
  simp_rw [hone]
  rw [lintegral_const, one_mul, show (volume : Measure (Fin (0 + 0) → ℝ)) =
    Measure.pi fun _ => volume from rfl, Measure.pi_of_empty (x := fun i => i.elim0),
    measure_univ]

/-- The limit of the empty diagrams is one. -/
theorem diagramLim_zero_zero (d : ℕ) (Γ : Measure (Rd d)) (α₀ : ℝ)
    (D : Fin (0 + 0) → Fin (0 + 0)) (t : ℝ) : diagramLim d Γ α₀ 0 0 D t = 1 := by
  unfold diagramLim
  simp_rw [diagram_zero_zero]
  exact tendsto_const_nhds.limUnder_eq

/-- `A_0(t) = 1` (main TeX line 5448). -/
theorem coeffALim_zero (d : ℕ) (Γ : Measure (Rd d)) (α₀ t : ℝ) : coeffALim d Γ α₀ 0 t = 1 := by
  simp [coeffALim, Pi2_zero_zero, diagramLim_zero_zero]

/-! ### Consequences of `MixedMoment` -/

section Consequences

variable {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}

/-- The odd case of `E:mixed-moment`. -/
theorem MixedMoment.moment_odd (h : MixedMoment d α₀ Γ P X u t) {m n : ℕ} (hodd : Odd (m + n)) :
    ∫ ω, X m ω * X n ω ∂P = 0 := by
  rw [(h.2.1 m n).2, Pi2_odd hodd, Finset.sum_empty]

/-- The case `m = n = 0` of `E:mixed-moment` equals one. -/
theorem MixedMoment.moment_zero_zero (h : MixedMoment d α₀ Γ P X u t) :
    ∫ ω, X 0 ω * X 0 ω ∂P = 1 := by
  rw [(h.2.1 0 0).2, Pi2_zero_zero, Finset.sum_singleton, diagramLim_zero_zero]
  simp

/-- Every mixed moment is nonnegative (each diagram is). -/
theorem MixedMoment.moment_nonneg (h : MixedMoment d α₀ Γ P X u t) (m n : ℕ) :
    0 ≤ ∫ ω, X m ω * X n ω ∂P := by
  rw [(h.2.1 m n).2]
  exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- The diagram coefficient `A_k(t)` is the TeX's
`A_k(t) = Σ_{m=0}^{2k} E[X_m X_{2k-m}]` (main TeX line 5448). -/
theorem MixedMoment.coeffA_eq (h : MixedMoment d α₀ Γ P X u t) (k : ℕ) :
    (coeffALim d Γ α₀ k t).toReal =
      ∑ m ∈ Finset.range (2 * k + 1), ∫ ω, X m ω * X (2 * k - m) ω ∂P := by
  unfold coeffALim
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [(h.2.1 m (2 * k - m)).2, ENNReal.toReal_sum]
    exact fun D hD => (h.1 m _ D hD).2
  · intro m _
    exact (ENNReal.sum_lt_top.2 fun D hD => lt_top_iff_ne_top.2 (h.1 m _ D hD).2).ne

/-- `E u² = Σ_k A_k(t)` (`E:full-second`, through the TeX's
`E u²(t,x) = Σ_{k ≥ 0} A_k(t)`, main TeX line 5451). -/
theorem MixedMoment.secondMoment_eq (h : MixedMoment d α₀ Γ P X u t) :
    ∫ ω, u ω ^ 2 ∂P = ∑' k, (coeffALim d Γ α₀ k t).toReal :=
  h.2.2.2.tsum_eq.symm

/-- `P:mixed` (main TeX lines 834-849) on the diagram model, with the TeX's
hypothesis `H:homog` and the supplied input `MixedMoment`: the odd moments
vanish, `E X_0² = 1`, every mixed moment is nonnegative, each
`A_k(t) = Σ_{m=0}^{2k} E[X_m X_{2k-m}]` is the diagram sum, and
`E u² = Σ_k A_k(t)` (`E:full-second`).  Everything is read off `MixedMoment`;
the hypothesis `H:homog` (under which `MixedMoment` is true) is carried but not
used by the proof. -/
theorem mixed_moment_paper {alpha : ℝ} {μ : Measure (Rd d)}
    (_hH : HomogHypothesis.HomogCovariance d alpha α₀ Γ μ) (h : MixedMoment d α₀ Γ P X u t) :
    (∀ m n : ℕ, Odd (m + n) → ∫ ω, X m ω * X n ω ∂P = 0) ∧
      ∫ ω, X 0 ω * X 0 ω ∂P = 1 ∧
      (∀ m n : ℕ, 0 ≤ ∫ ω, X m ω * X n ω ∂P) ∧
      (∀ k : ℕ, (coeffALim d Γ α₀ k t).toReal =
        ∑ m ∈ Finset.range (2 * k + 1), ∫ ω, X m ω * X (2 * k - m) ω ∂P) ∧
      ∫ ω, u ω ^ 2 ∂P = ∑' k, (coeffALim d Γ α₀ k t).toReal :=
  ⟨fun _ _ hodd => h.moment_odd hodd, h.moment_zero_zero, h.moment_nonneg, h.coeffA_eq,
    h.secondMoment_eq⟩

end Consequences

end StratonovichHAMSecondMoment.DiagramModel
