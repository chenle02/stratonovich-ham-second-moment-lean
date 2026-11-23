module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item L19-0 (interface; approved by Le on 2026-11-21 with the default answers to all
thirteen decisions: scope L19-0, A..E, G; field design "any probability space with a centered
Gaussian field of covariance `E:pairing-source-covariance`, plus the constructed instance M9";
self-contained Mathlib-only isonormal layer (no separate private library); "manuscript hypotheses"
classification; `S_n(g_n)` read as the common-width limit; `u := Σ_n X_n`; d = 1, 2, 3; only the
true named inputs `SourceNoise`, `TerminalReversal` as fallbacks).  The frozen Lean objects and
statement shapes for the item agents A, B, C, D, E and G of the `L²` construction.  Nothing in
this module proves an item target; the only assembly proved here is `sourceField_of_parts`
(A and B give the M9 instance target), which is pure bookkeeping.

TeX anchors: main file `notes/notes_stratonovich_ham_second_moment.tex` at revision 0788ddee
(book 1.1.0; the same line numbers at edf7085f, book 1.1.3), read with
`git show 0788ddee:notes/<file>.tex`:
* `E:expansion` 542-549 (`u = Σ_n S_n(g_n)`, `g_n`, the terminal ordered simplex);
* `X_n = S_n(g_n)`, `X_0 = 1` 796;
* `E:mixed-diagram` 814-824, conventions 825-832;
* `P:mixed` 834-849 (`E:mixed-moment` 836-842, the `m = n = 0` clause 843, `E:full-second`
  844-847), proof 851-927 (Step 1 858-882, Step 2 885-905 with the reversal 888-905, the
  sentence "The same transformation holds before removing noise smoothing" 903; Step 3
  908-926);
* `E:pairing-source-covariance` 1352-1370 (Remark item (iii): common-prefix source convention,
  the source's (2.11) p. 9 cited at 1352-1353; cap minimum 1356-1357; display 1360-1370);
* the regularization paragraph 1643-1655 (`Y_n^a` 1643-1647, Bochner integrals and the Wick
  bound 1647-1650, Green mass 1650-1651, d = 3 Green-first `L²` limit 1651-1655);
* `L:joint-fixed-order` 1853-1862 (the `L²` limit 1858-1860, Green-first 1860-1861), proof
  1864-1966 with Step 4 1949-1965 (`‖Y^a - Y^b‖² → 0` 1956-1959, Green-before-noise 1960-1963,
  common widths = the Stratonovich definition 1963-1964);
* `E:crude-norms` 1973; `L:vertex-crude` 2062-2074 (`E:vertex-crude` 2065-2068,
  `E:vertex-summability` 2071-2073), proof 2076-2145.

Model choice M9 (the source field, decision 2).  Points are `SrcPt d = ([0,∞) × ℝ^d) × W₊`, a
space-time point with a positive width pair `w = (ε, δ) ∈ W₊ = (0,∞)²` (`PosW`).  The field
hypothesis `SourceField α₀ Γ P W` is: `W` is a `FiniteWick.CenteredGaussianField` on `SrcPt d`
with covariance `srcCov α₀ Γ`,
`srcCov((s,x,ε,δ), (s',y,ε',δ')) = κ_{δ∨δ'}(s - s') γ_{ε+ε'}(x - y)`,
`κ_δ = kerA α₀ (capSet δ)` (L18's M8 kernel, the TeX's `κ_δ` of 1366-1367), `γ_b = gammaEps Γ b`
(`p_b * Γ`).  This is exactly the TeX's statement 1360-1365 about the positive-width source
fields `Y_{ε,δ}` (= `W_{ε,δ}` at 1647): one probability space carries all of them jointly.
The constructed instance (`SourceModel`, `SourceFieldTarget`, `m9`) is produced by items A and B
(`sourceField_of_parts`).  Relation to M4/M8: no M4 diagram is realized at positive widths (the
temporal width `0` has infinite variance); the terminal pairing integrals at positive widths are
M8 diagrams `wickF … (capDom δ) ε` after the chain reversal (C), and M4 enters only in the limit
through `JointFixedOrder.joint_limit_aux` + `m8_m4_identity` (E).

Readings (for the fidelity review):
* `Y_n^a(t,x)` (`Ya`) is the `L²(Ω)`-valued Bochner integral of `∏_j W(z_j, a_j)` against the
  terminal chain measure `g_n^{t,x}` (`TerminalWickInputs.chainMeasure`), with the width `a_j`
  attached to vertex `j` (`attach`); vertex `n-1` is the one next to the terminal point `(t,x)`.
* "all widths tend to zero at arbitrary relative rates" for the `2n` real widths of `Y_n^a` is
  `widthFilter n ×ˢ widthFilter n` (L18's filter; spatial vector first); the junk value of
  `posW` outside the positive orthant is never seen by this filter (`eventually_posW`);
* "common noise widths" (1963-1964) is the filter `𝓝[>] 0 ×ˢ 𝓝[>] 0` on `(ε, δ)`, all
  vertices carrying `(ε, δ)`; `S_n(g_n)(t,x)` (`stratInt`) is the limit along it (decision 5);
* `X_n = stratInt` for `n ≥ 1`, `X_0 = Y_0` (`= 1` a.s., `Ya_zero`), and `u = Σ_n X_n` in `L²`
  (`uL2`, decision 6); the real-valued `srcX` uses the constant `1` at order `0` (as
  `LowAlphaUpper.FirstMomentSeries` requires `X 0 ω = 1` for every `ω`);
* `E:mixed-moment`'s `J_{m,n,D}(t)` is M4's `diagramLim` (as in `DiagramModel.MixedMoment`).

Proved here (interface sanity only): `PosW.eps_pos`, `PosW.del_pos`, `posW_of_pos`,
`eventually_posW`, `srcCov_def`, `srcCov_diag`, `srcCov_nonneg`, `srcCov_comm`,
`kerA_capSet_ne_top`, `centeredGaussianField_comp`, `sourceField_of_parts`, `Ya_zero`,
`XL2_zero`, `XL2_succ`, `srcX_zero`, `srcX_succ`, `tendsto_unique_widths`, `qn_zero`,
`qn_nonneg`, and the named instances `instMeasurableSpaceSourceModel`,
`instIsProbabilitySourceModel`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WickFinal
public import StratonovichHAMSecondMoment.TerminalWickRegularization
public import StratonovichHAMSecondMoment.LowAlphaUpper

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.SourceInterface

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField pairWeight)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure)
open TerminalWickRegularization (chainMeasureReg)
open WickInterface (kerA capSet capDom wickF widthFilter posOrthant)
open LowAlphaConvolution (gammaEps)
open DiagramModel (Pi2 rev revPairing diagramLim)

variable {d : ℕ}

/-! ### M9: points with widths and the source covariance (TeX 1352-1370) -/

/-- A positive width pair `w = (ε, δ)`, `ε, δ > 0` (TeX 1643-1644: "`a = (ε,δ) > 0`"). -/
abbrev PosW : Type := {w : ℝ × ℝ // 0 < w.1 ∧ 0 < w.2}

/-- The spatial (heat) width `ε` of a width pair. -/
def PosW.eps (w : PosW) : ℝ := w.1.1

/-- The temporal width `δ` of a width pair (Laplace cap `δ⁻¹`, TeX 1366-1367). -/
def PosW.del (w : PosW) : ℝ := w.1.2

/-- The points of the source field: a time `s ≥ 0`, a place `x ∈ ℝ^d` and a positive width
pair (TeX 1362-1363: `Y_{ε_j,δ_j}(s,x)`). -/
abbrev SrcPt (d : ℕ) : Type := (↥(Set.Ici (0 : ℝ)) × Rd d) × PosW

/-- **`E:pairing-source-covariance`** (TeX 1360-1370 at revision edf7085f (book 1.1.3)):
`E[Y_{ε_j,δ_j}(s,x) Y_{ε_h,δ_h}(t,y)] = κ_{δ_j∨δ_h}(s-t) (p_{ε_j+ε_h} * Γ)(x-y)`, with
`κ_δ(u) = Γ_E(a)⁻¹ ∫_0^{δ⁻¹} e^{-λ|u|} λ^{a-1} dλ`, `a = α₀` (`kerA α₀ (capSet δ)`, finite for
`δ > 0`: `kerA_capSet_ne_top`). -/
def srcCov (α₀ : ℝ) (Γ : Measure (Rd d)) (p q : SrcPt d) : ℝ :=
  (kerA α₀ (capSet (max p.2.del q.2.del)) ((p.1.1 : ℝ) - (q.1.1 : ℝ))).toReal *
    gammaEps Γ (p.2.eps + q.2.eps) (p.1.2 - q.1.2)

/-- **The field hypothesis of M9** (TeX 1352-1370 at revision edf7085f (book 1.1.3)): `W` is a
centered real Gaussian field on all points with positive widths, jointly on one probability
space, with covariance `E:pairing-source-covariance`.  Every theorem of L19 takes it as its
hypothesis on the noise (decision 2); `SourceFieldTarget` (items A, B) shows it satisfiable. -/
abbrev SourceField (α₀ : ℝ) (Γ : Measure (Rd d)) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : SrcPt d → Ω → ℝ) : Prop :=
  CenteredGaussianField W (srcCov α₀ Γ) P

/-- **The constructed model M9**: a probability space carrying a source field. -/
structure SourceModel (d : ℕ) (α₀ : ℝ) (Γ : Measure (Rd d)) where
  /-- The sample space. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The probability measure. -/
  P : Measure Ω
  /-- `P` is a probability measure. -/
  isProb : IsProbabilityMeasure P
  /-- The field `W(s, x, ε, δ)`. -/
  W : SrcPt d → Ω → ℝ
  /-- The field hypothesis. -/
  field : SourceField α₀ Γ P W

/-- The σ-algebra of a source model. -/
instance instMeasurableSpaceSourceModel {α₀ : ℝ} {Γ : Measure (Rd d)}
    (M : SourceModel d α₀ Γ) : MeasurableSpace M.Ω := M.mΩ

/-- The measure of a source model is a probability measure. -/
instance instIsProbabilitySourceModel {α₀ : ℝ} {Γ : Measure (Rd d)}
    (M : SourceModel d α₀ Γ) : IsProbabilityMeasure M.P := M.isProb

/-! ### The terminal chain integrals with vertexwise widths (TeX 1643-1655) -/

/-- Attach the width `a_j` to vertex `j` of a terminal chain `z : Fin n → [0,t] × ℝ^d`. -/
def attach {t : ℝ} {n : ℕ} (a : Fin n → PosW) (z : Fin n → Pt d t) : Fin n → SrcPt d :=
  fun j => ((⟨((z j).1 : ℝ), (z j).1.2.1⟩, (z j).2), a j)

section Chains

variable {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- **`Y_n^a(t,x)`** (TeX 1643-1650 at revision edf7085f (book 1.1.3)): the ordered terminal
integral with kernel `g_n` (`chainMeasure d n t ht x`, TeX `E:terminal-chain-measure`) and the
field `W_{ε_j,δ_j}(s_j, y_j)` at vertex `j`, as the `L²(Ω)`-valued Bochner integral of
`∏_j W(s_j, y_j, a_j)`.  For `n = 0` it is `1` a.s. (`Ya_zero`). -/
def Ya (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {n : ℕ}
    (a : Fin n → PosW) : Lp ℝ 2 P :=
  ∫ z, prodL2 hW (attach a z) ∂chainMeasure d n t ht x

/-- **`Y_n^{a,η}(t,x)`**, the Green-smoothed terminal integral (TeX 1651-1655): the chain
measure with the Green kernels `p_η * G` (`TerminalWickRegularization.chainMeasureReg`,
common-noise construction; `η = 0` is the unsmoothed chain measure). -/
def YaReg (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {n : ℕ}
    (a : Fin n → PosW) (η : ℝ) : Lp ℝ 2 P :=
  ∫ z, prodL2 hW (attach a z) ∂chainMeasureReg d n t ht x η

end Chains

/-- Real width vectors `(ε, δ)` as width pairs; the value `(1, 1)` off the positive orthant is
junk, never seen by the width filters (`eventually_posW`). -/
def posW {n : ℕ} (ε δ : Fin n → ℝ) (j : Fin n) : PosW :=
  if h : 0 < ε j ∧ 0 < δ j then ⟨(ε j, δ j), h⟩ else ⟨(1, 1), by norm_num⟩

section Limits

variable {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- `Y_n^a` at real vertexwise widths `ε` (spatial) and `δ` (temporal). -/
def Yw (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {n : ℕ}
    (ε δ : Fin n → ℝ) : Lp ℝ 2 P :=
  Ya hW t ht x (posW ε δ)

/-- `Y_n` at the common noise widths `p = (ε, δ)` on every vertex (TeX 1963-1964). -/
def Ycom (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (n : ℕ)
    (p : ℝ × ℝ) : Lp ℝ 2 P :=
  Yw hW t ht x (fun _ : Fin n => p.1) (fun _ : Fin n => p.2)

/-- **`S_n(g_n)(t,x)`, the multiple Stratonovich integral** (decision 5; TeX 1859-1860,
1963-1964 at revision edf7085f (book 1.1.3)): the `L²` limit of `Y_n` at common noise widths
`(ε, δ) → (0,0)`, `ε, δ > 0` (`limUnder`; the D target proves the limit exists). -/
def stratInt (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (n : ℕ) :
    Lp ℝ 2 P :=
  limUnder (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (Ycom hW t ht x n)

/-- **`X_n(t,x)` in `L²(Ω)`** (TeX 796): `X_0 = Y_0` (`= 1` a.s.), `X_{n+1} = S_{n+1}(g_{n+1})`. -/
def XL2 (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) : ℕ → Lp ℝ 2 P
  | 0 => Ya hW t ht x (Fin.elim0 : Fin 0 → PosW)
  | n + 1 => stratInt hW t ht x (n + 1)

/-- **`u(t,x) = Σ_n X_n(t,x)`** in `L²(Ω)` (`E:expansion`, TeX 542-549, with `X_n` at 796;
decision 6).  `tsum`: the junk value `0` if not summable; E proves summability. -/
def uL2 (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) : Lp ℝ 2 P :=
  ∑' n, XL2 hW t ht x n

/-- The real random variables `X_n` handed to `MixedMoment` / `FirstMomentSeries`: the constant
`1` at order `0`, a representative of `X_n` otherwise. -/
def srcX (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (n : ℕ) : Ω → ℝ :=
  if n = 0 then fun _ => 1 else (XL2 hW t ht x n : Ω → ℝ)

/-- A representative of `u(t,x)`. -/
def srcU (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) : Ω → ℝ :=
  (uL2 hW t ht x : Ω → ℝ)

end Limits

/-! ### Terminal pairing integrals and widths of the reversed chains (TeX 885-905) -/

/-- The concatenated vertex widths of two chains: `ε` part. -/
def epsV {m n : ℕ} (a : Fin m → PosW) (b : Fin n → PosW) (i : Fin (m + n)) : ℝ :=
  (Fin.append a b i).eps

/-- The concatenated vertex widths of two chains: `δ` part. -/
def delV {m n : ℕ} (a : Fin m → PosW) (b : Fin n → PosW) (i : Fin (m + n)) : ℝ :=
  (Fin.append a b i).del

/-- **The terminal pairing integral at positive vertexwise widths** (TeX 4315-4328 with the two
chains carrying widths `a`, `b`; regularization paragraph 1643-1650): the integral against
`g_m^{t,x} ⊗ g_n^{t,x}` of `∏_{{i,j} ∈ D} srcCov(τ_i, τ_j)`, `τ = Fin.append` of the two
width-attached tuples. -/
def srcPairing (α₀ : ℝ) (Γ : Measure (Rd d)) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {m n : ℕ}
    (a : Fin m → PosW) (b : Fin n → PosW) (D : Fin (m + n) → Fin (m + n)) : ℝ :=
  ∫ q, pairWeight (fun i j => srcCov α₀ Γ (Fin.append (attach a q.1) (attach b q.2) i)
      (Fin.append (attach a q.1) (attach b q.2) j)) Finset.univ D
    ∂((chainMeasure d m t ht x).prod (chainMeasure d n t ht x))

/-- `q_n(t) = e^{θ₀ t} C^{n/2} t^n / √(n!)` (`E:vertex-crude`, TeX 2067). -/
def qn (C θ₀ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (θ₀ * t) * Real.sqrt C ^ n * t ^ n / Real.sqrt (n ! : ℝ)

/-! ### Frozen targets: item A (isonormal map; Mathlib-level foundation) -/

/-- **A target, the isonormal map**: every real Hilbert space `H` carries, on some probability
space, a centered Gaussian field indexed by `H` with covariance the inner product (so the law of
every finite family is `multivariateGaussian 0` of its Gram matrix).  No TeX claim (Mathlib-level
foundation for M9; decision 3 (i)); with `centeredGaussianField_comp` it gives the field of any
feature map. -/
def IsonormalTarget : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : H → Ω → ℝ),
      IsProbabilityMeasure P ∧ CenteredGaussianField W (fun h g => inner ℝ h g) P

/-! ### Frozen targets: item B (`E:pairing-source-covariance`, TeX 1352-1370) -/

/-- **B target, the feature representation of `E:pairing-source-covariance`** (TeX 1352-1370 at
revision edf7085f (book 1.1.3); cap minimum 1356-1357, heat semigroup 1357-1359): under
`H:homog` there are a real Hilbert space `H` and a feature map `feat : SrcPt d → H` with Gram
form `⟪feat p, feat q⟫ = srcCov α₀ Γ p q` (hence `srcCov` is positive semidefinite).  Route
(decision 3, disclosed): temporal features `1{λ ∈ capSet δ} h_λ(s, r)` (L17's
decaying-exponential feature) in `L²(ν ⊗ dr)`, the real spatial feature
`e^{-ε|ξ|²/2}(cos ξ·x + sin ξ·x)` against the even spectral measure `μ` (`H:homog`'s `μ_even`),
and their pointwise product in `L²(ν ⊗ dr ⊗ μ)` (proved in `SourceFeatures`). -/
def SourceFeatureTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (feat : SrcPt d → H), ∀ p q : SrcPt d, inner ℝ (feat p) (feat q) = srcCov α₀ Γ p q

/-- **B target, continuity of the covariance at fixed widths** (used by C, and by D's
`green_first`, for the strong measurability of `Y_n^a`, as `L:terminal-wick`'s mean-square
continuity, TeX 4294-4296): under `H:homog`, for fixed width pairs `w, w'`,
`((s,x),(s',y)) ↦ srcCov((s,x,w),(s',y,w'))` is continuous. -/
def SourceCovContinuousTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ w w' : PosW, Continuous fun pq : (↥(Set.Ici (0 : ℝ)) × Rd d) × (↥(Set.Ici (0 : ℝ)) × Rd d) =>
      srcCov α₀ Γ (pq.1, w) (pq.2, w')

/-- **The M9 instance target** (TeX 1352-1370: the source's positive-width fields exist jointly):
under `H:homog` a source model exists.  Proved from A and B by `sourceField_of_parts`. -/
def SourceFieldTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    Nonempty (SourceModel d α₀ Γ)

/-- **Named input (fallback for A/B): `SourceNoise`** — the existence of the source's joint
positive-width fields with covariance `E:pairing-source-covariance` (the source's (2.11), p. 9,
and (2.24), p. 13, as cited at TeX 1352-1353 at revision edf7085f (book 1.1.3)).  True (it is the
TeX claim); used only if A or B overruns (not used in wave L19: `SourceFinal.source_field_l19` proves the
content). -/
structure SourceNoise (d : ℕ) : Prop where
  holds : SourceFieldTarget d

/-- **M9, the constructed model**, chosen from a proof of `SourceFieldTarget d`. -/
def m9 (h : SourceFieldTarget d) {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) : SourceModel d α₀ Γ :=
  Classical.choice (h hH)

/-! ### Frozen targets: item C (two-family terminal Wick and reversal, TeX 858-905, 1643-1650) -/

/-- **C target, the finite Wick formula at positive vertexwise widths** (TeX 1643-1650 and
`P:mixed` Step 1, 858-882 at revision edf7085f (book 1.1.3); `L:terminal-wick`'s formula
`E:terminal-wick-formula` 4310-4313, proved in its Step 2 4365-4378, with two width
families): under `H:homog`, for every source field, `t > 0`, `x`, and width vectors `a`, `b`
of lengths `m`, `n`, the product `Y_m^a Y_n^b` is integrable and
`E[Y_m^a Y_n^b] = Σ_{D ∈ Π} T_{m,n,D}^{a,b}` (zero at odd `m + n`: `Pi2_odd`). -/
def TerminalWickWTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d)
      (m n : ℕ) (a : Fin m → PosW) (b : Fin n → PosW),
      Integrable (fun ω => Ya hW t ht.le x a ω * Ya hW t ht.le x b ω) P ∧
        ∫ ω, Ya hW t ht.le x a ω * Ya hW t ht.le x b ω ∂P =
          ∑ D ∈ Pi2 m n, srcPairing α₀ Γ t ht.le x a b D

/-- **C target, the reversal identity at positive widths** (`P:mixed` Step 2, TeX 888-905 at
revision edf7085f (book 1.1.3): `s'_j = t - s_{m+1-j}`, `y'_j = x - y_{m+1-j}` on each chain,
the involution `ρ` (`DiagramModel.rev`) and the pairing bijection `D ↦ ρDρ`
(`DiagramModel.revPairing`); "The same transformation holds before removing noise smoothing",
903): under `H:homog`, at `t > 0`, every terminal pairing integral is the M8 diagram
`F_{ε',δ',ρDρ}(t,t)` with the reversed vertex widths `ε' = ε ∘ ρ`, `δ' = δ ∘ ρ`, and the latter
is finite. -/
def TerminalReversalTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (t : ℝ) (ht : 0 < t) (x : Rd d) (m n : ℕ) (a : Fin m → PosW) (b : Fin n → PosW)
      (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
      wickF (waveGreen d) Γ α₀ (capDom fun i => delV a b (rev m n i))
          (fun i => epsV a b (rev m n i)) m (revPairing m n D) t t ≠ ⊤ ∧
        srcPairing α₀ Γ t ht.le x a b D =
          (wickF (waveGreen d) Γ α₀ (capDom fun i => delV a b (rev m n i))
            (fun i => epsV a b (rev m n i)) m (revPairing m n D) t t).toReal

/-- **Named input (fallback for C): `TerminalReversal`** (TeX 888-905 at revision edf7085f
(book 1.1.3), at positive widths, 903).  True (it is the TeX claim); used only if C overruns (not used in wave L19:
`SourceReversal.terminal_reversal` proves the content). -/
structure TerminalReversal (d : ℕ) : Prop where
  holds : TerminalReversalTarget d

/-- **C target, the headline: mixed moments at positive widths are M8 diagram sums** (the
composite of `TerminalWickWTarget` and `TerminalReversalTarget` with
`DiagramModel.sum_revPairing`; TeX 858-905, Step 4's first sentence 1951-1953): under
`H:homog`, `E[Y_m^a Y_n^b] = Σ_{D ∈ Π} F_{ε∘ρ, δ∘ρ, D}(t,t)` (all terms finite). -/
def TerminalMixedMomentTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d)
      (m n : ℕ) (a : Fin m → PosW) (b : Fin n → PosW),
      Integrable (fun ω => Ya hW t ht.le x a ω * Ya hW t ht.le x b ω) P ∧
        ∫ ω, Ya hW t ht.le x a ω * Ya hW t ht.le x b ω ∂P =
          ∑ D ∈ Pi2 m n, (wickF (waveGreen d) Γ α₀ (capDom fun i => delV a b (rev m n i))
            (fun i => epsV a b (rev m n i)) m D t t).toReal

/-! ### Frozen targets: item D (`L:joint-fixed-order`, `L²` half, TeX 1858-1861, 1949-1965) -/

/-- **D target, the joint `L²` limit and the Stratonovich integral** (`L:joint-fixed-order`,
TeX 1858-1860 at revision edf7085f (book 1.1.3); Step 4 1949-1965): under `H:homog`, for every
source field, `n ≥ 1`, `t > 0`, `x`: `Y_n^a(t,x)` converges in `L²` as all `2n` positive
vertexwise widths tend to zero at arbitrary relative rates, and its limit is `S_n(g_n)(t,x)`,
the limit at common noise widths (which therefore exists).  Uniqueness of the limit is
`tendsto_unique_widths`. -/
def FixedOrderL2Target (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d)
      (n : ℕ), 1 ≤ n →
      Tendsto (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Yw hW t ht.le x p.1 p.2)
          (widthFilter n ×ˢ widthFilter n) (𝓝 (stratInt hW t ht.le x n)) ∧
        Tendsto (Ycom hW t ht.le x n) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
          (𝓝 (stratInt hW t ht.le x n))

/-- **D target, Green smoothing removed before noise smoothing** (TeX 1651-1655 and 1860-1861,
1960-1963 at revision edf7085f (book 1.1.3)): under `H:homog`, at fixed positive vertexwise
noise widths, the Green-smoothed `Y_n^{a,η}` converge in `L²` to `Y_n^a` as `η ↓ 0`.  The TeX's
sentence is the case d = 3; the target is stated for d = 1, 2, 3 (same route, the d = 1, 2
cases are not used by the TeX; disclosed). -/
def GreenFirstTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d)
      (n : ℕ) (a : Fin n → PosW),
      Tendsto (fun η => YaReg hW t ht.le x a η) (𝓝[>] (0 : ℝ)) (𝓝 (Ya hW t ht.le x a))

/-! ### Frozen targets: item E (`P:mixed`, `E:expansion`, the named inputs; TeX 834-927) -/

/-- **E target, the identification `b_D = J_{m,n,D}`** (`b_D`: `L:joint-fixed-order` Step 3, TeX
1933-1943; 1855-1858 with 825-832 and Step 2's
"Passing to the finitely many diagram limits", 903-905): under `H:homog`, the joint limit of
the M8 diagrams is M4's `diagramLim` (route: `JointFixedOrder.joint_limit_aux` with
`WickFinal.spatial_wick_measures_l18`, `joint_temporal_tail_l18`, then `m8_m4_identity` and
`tendsto_half_widthFilter`). -/
def DiagramLimIdentTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ D ∈ Pi2 m n, ∀ t : ℝ, 0 < t →
      Tendsto (fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → ℝ) =>
          wickF (waveGreen d) Γ α₀ (capDom p.2) p.1 m D t t)
        (widthFilter (m + n) ×ˢ widthFilter (m + n)) (𝓝 (diagramLim d Γ α₀ m n D t))

/-- **E target, `E:expansion` in `L²`** (TeX 542-549 with 796, and `P:mixed` Step 3 908-916 at
revision edf7085f (book 1.1.3)): under `H:homog`, the `L²` norms of the `X_n(t,x)` are summable
and `U_N = Σ_{n ≤ N} X_n → u` in `L²`. -/
def ExpansionL2Target (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d),
      Summable (fun n => ‖XL2 hW t ht.le x n‖) ∧ HasSum (XL2 hW t ht.le x) (uL2 hW t ht.le x)

/-- **E target, `P:mixed`** (TeX 834-849 at revision edf7085f (book 1.1.3); proof 851-927):
under `H:homog`, for every source field, `t > 0` (the reading of `P:mixed`, whose display
shows no restriction on `t`: the construction and `L:joint-fixed-order` 1858 take `t > 0`, and
`t = 0` is trivial) and `x`, the constructed `X_n(t,x)` and
`u(t,x) = Σ_n X_n(t,x)` satisfy `DiagramModel.MixedMoment`: finite diagram limits,
`E:mixed-moment` (836-842; integrability, the pairing sum of `J_{m,n,D}(t)`, zero at odd order,
one at `m = n = 0`), `u² ∈ L¹` and `E:full-second` (844-847) as a `HasSum` of nonnegative
terms. -/
def MixedTermsTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d),
      DiagramModel.MixedMoment d α₀ Γ P (srcX hW t ht.le x) (srcU hW t ht.le x) t

/-- **E target, `FirstMomentSeries` for the constructed objects** (TeX 796, 542-549; used at
5856-5857 at revision edf7085f (book 1.1.3)): `X_0 = 1` pointwise, `u ∈ L¹` and
`E u = Σ_n E X_n`. -/
def FirstMomentSeriesTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d),
      LowAlphaUpper.FirstMomentSeries P (srcX hW t ht.le x) (srcU hW t ht.le x)

/-! ### Frozen targets: item G (`L:vertex-crude`, TeX 2062-2074) -/

/-- **G target, deterministic half** (`L:vertex-crude` Steps 1-2, TeX 2083-2135 at revision
edf7085f (book 1.1.3)): under `H:homog` there are `C, θ₀ > 0` such that for `n ≥ 1`, `t > 0`
and all positive vertexwise widths on the `2n` vertices,
`Σ_{D ∈ Π_n} F_{ε,δ,D}(t,t) ≤ q_n(t)²`.  (The TeX applies it to the widths of `Y_n^a` copied to
the second chain and reversed; its edgewise argument covers arbitrary widths, which is what is
stated.) -/
def VertexDiagramTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ (n : ℕ), 1 ≤ n → ∀ t : ℝ, 0 < t →
      ∀ ε δ : Fin (n + n) → ℝ, (∀ i, 0 < ε i) → (∀ i, 0 < δ i) →
        ∑ D ∈ Pi2 n n, wickF (waveGreen d) Γ α₀ (capDom δ) ε n D t t ≤
          ENNReal.ofReal (qn C θ₀ n t ^ 2)

/-- **G target, `L:vertex-crude`** (TeX 2062-2074 at revision edf7085f (book 1.1.3)): under
`H:homog` there are `C < ∞` and `θ₀ > 0` such that, for every source field, all positive
vertexwise widths, `n ≥ 1`, `t > 0` and `x`, `‖Y_n^a(t,x)‖₂ ≤ q_n(t)` (`E:vertex-crude`); the
bound holds for `X_n(t,x)`, `n ≥ 0`, with `q_0(t) = e^{θ₀t}`; and for each `T`,
`Σ_n √(n+1) q_n(T) < ∞` (`E:vertex-summability`, stated for every real `T`). -/
def VertexCrudeTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d)
        (n : ℕ), 1 ≤ n → ∀ a : Fin n → PosW, ‖Ya hW t ht.le x a‖ ≤ qn C θ₀ n t) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d)
        (n : ℕ), ‖XL2 hW t ht.le x n‖ ≤ qn C θ₀ n t) ∧
      ∀ T : ℝ, Summable fun n : ℕ => Real.sqrt ((n : ℝ) + 1) * qn C θ₀ n T

/-! ### Sanity lemmas (interface only) -/

section Sanity

theorem PosW.eps_pos (w : PosW) : 0 < w.eps := w.2.1

theorem PosW.del_pos (w : PosW) : 0 < w.del := w.2.2

/-- On the positive orthant `posW` is the honest width pair. -/
theorem posW_of_pos {n : ℕ} {ε δ : Fin n → ℝ} (j : Fin n) (h : 0 < ε j ∧ 0 < δ j) :
    posW ε δ j = ⟨(ε j, δ j), h⟩ := by
  unfold posW; simp [h]

/-- The width filters only see honest width pairs. -/
theorem eventually_posW (n : ℕ) :
    ∀ᶠ p : (Fin n → ℝ) × (Fin n → ℝ) in widthFilter n ×ˢ widthFilter n,
      ∀ j, (posW p.1 p.2 j).eps = p.1 j ∧ (posW p.1 p.2 j).del = p.2 j := by
  have h : ∀ᶠ v : Fin n → ℝ in widthFilter n, v ∈ posOrthant n := self_mem_nhdsWithin
  filter_upwards [h.prod_mk h] with p hp j
  have hj : 0 < p.1 j ∧ 0 < p.2 j := ⟨hp.1 j (mem_univ _), hp.2 j (mem_univ _)⟩
  rw [posW_of_pos j hj]
  exact ⟨rfl, rfl⟩

section Cov

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

theorem srcCov_def (p q : SrcPt d) :
    srcCov α₀ Γ p q = (kerA α₀ (capSet (max p.2.del q.2.del)) ((p.1.1 : ℝ) - (q.1.1 : ℝ))).toReal *
      gammaEps Γ (p.2.eps + q.2.eps) (p.1.2 - q.1.2) := rfl

/-- The variance depends only on the widths: `κ_δ(0) γ_{2ε}(0)` (finitely many widths give a
finite variance bound, TeX 1649-1650). -/
theorem srcCov_diag (p : SrcPt d) :
    srcCov α₀ Γ p p = (kerA α₀ (capSet p.2.del) 0).toReal * gammaEps Γ (p.2.eps + p.2.eps) 0 := by
  simp [srcCov]

/-- The source covariance is nonnegative. -/
theorem srcCov_nonneg (p q : SrcPt d) : 0 ≤ srcCov α₀ Γ p q :=
  mul_nonneg ENNReal.toReal_nonneg
    (LowAlphaConvolution.gammaEps_nonneg Γ (add_pos p.2.eps_pos q.2.eps_pos).le _)

/-- The source covariance is symmetric (evenness of `κ` and of `Γ`). -/
theorem srcCov_comm (hH : HomogCovariance d alpha α₀ Γ μ) (p q : SrcPt d) :
    srcCov α₀ Γ p q = srcCov α₀ Γ q p := by
  unfold srcCov WickInterface.kerA
  rw [max_comm, add_comm q.2.eps, ← LowAlphaUpper.gammaEps_neg hH.Γ_even _ (p.1.2 - q.1.2),
    neg_sub, abs_sub_comm]

/-- The capped kernel is finite at positive width (`κ_δ(u) ≤ κ_δ(0) < ∞`). -/
theorem kerA_capSet_ne_top (hH : HomogCovariance d alpha α₀ Γ μ) {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    kerA α₀ (capSet δ) u ≠ ⊤ :=
  ne_top_of_le_ne_top (JointFixedOrder.kerA_capSet_zero_ne_top hH.alpha0_pos hδ)
    (JointFixedOrder.kerA_le_zero α₀ (WickInterface.measurableSet_capSet δ)
      (WickInterface.capSet_subset_Ioi δ) u)

end Cov

/-- A centered Gaussian field restricted along any map of index sets is a centered Gaussian
field (the feature-map step: `feat : X → H` and the isonormal field on `H`). -/
theorem centeredGaussianField_comp {X Y Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : X → Ω → ℝ} {K : X → X → ℝ} (hW : CenteredGaussianField W K P) (feat : Y → X) :
    CenteredGaussianField (fun y => W (feat y)) (fun y y' => K (feat y) (feat y')) P :=
  ⟨fun n p => hW.psd n (feat ∘ p), fun n p => hW.law n (feat ∘ p)⟩

/-- **A and B give the M9 instance target** (bookkeeping: the isonormal field on the feature
space of `SourceFeatureTarget`, composed with the feature map). -/
theorem sourceField_of_parts (hA : IsonormalTarget) (hB : SourceFeatureTarget d) :
    SourceFieldTarget d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨H, i1, i2, i3, feat, hfeat⟩ := hB hH
  obtain ⟨Ω, mΩ, P, W, hP, hW⟩ := hA H
  have hc := centeredGaussianField_comp hW feat
  have hK : (fun p q : SrcPt d => inner ℝ (feat p) (feat q)) = srcCov α₀ Γ := by
    funext p q; exact hfeat p q
  rw [hK] at hc
  exact ⟨{ Ω := Ω, mΩ := mΩ, P := P, isProb := hP, W := fun p => W (feat p), field := hc }⟩

section Objects

variable {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- `Y_0 = 1` almost surely (TeX 1647: "put `Y_0 = 1`"; the terminal chain measure of order `0`
has mass `t^0/0! = 1`). -/
theorem Ya_zero (hd : d = 1 ∨ d = 2 ∨ d = 3) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t)
    (x : Rd d) (a : Fin 0 → PosW) :
    (Ya hW t ht x a : Ω → ℝ) =ᵐ[P] fun _ => 1 := by
  have h0 : chainMeasure d 0 t ht x univ = 1 := by
    rw [TerminalWickInputs.chainMeasure_univ_eq_chainMass d hd 0 t ht x,
      TerminalWick.chainMass_eq d hd 0 t ht]
    simp
  unfold Ya
  rw [integral_unique, measureReal_def, h0, ENNReal.toReal_one, one_smul]
  filter_upwards [TerminalWick.coeFn_prodL2 hW (attach a (default : Fin 0 → Pt d t))] with ω h
  rw [h]
  simp

theorem XL2_zero (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) :
    XL2 hW t ht x 0 = Ya hW t ht x (Fin.elim0 : Fin 0 → PosW) := rfl

theorem XL2_succ (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (n : ℕ) :
    XL2 hW t ht x (n + 1) = stratInt hW t ht x (n + 1) := rfl

theorem srcX_zero (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (ω : Ω) :
    srcX hW t ht x 0 ω = 1 := by
  simp [srcX]

theorem srcX_succ (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (n : ℕ) :
    srcX hW t ht x (n + 1) = (stratInt hW t ht x (n + 1) : Ω → ℝ) := by
  simp [srcX, XL2_succ]

/-- "a unique joint `L²` limit" (TeX 1858-1859): limits along the joint width filter are unique. -/
theorem tendsto_unique_widths {n : ℕ} {f : (Fin n → ℝ) × (Fin n → ℝ) → Lp ℝ 2 P}
    {X X' : Lp ℝ 2 P} (h : Tendsto f (widthFilter n ×ˢ widthFilter n) (𝓝 X))
    (h' : Tendsto f (widthFilter n ×ˢ widthFilter n) (𝓝 X')) : X = X' :=
  tendsto_nhds_unique h h'

end Objects

theorem qn_zero (C θ₀ t : ℝ) : qn C θ₀ 0 t = Real.exp (θ₀ * t) := by
  simp [qn]

theorem qn_nonneg {C θ₀ t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ qn C θ₀ n t := by
  unfold qn; positivity

end Sanity

end StratonovichHAMSecondMoment.SourceInterface
