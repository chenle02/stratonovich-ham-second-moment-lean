module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-0 (interface; approved by Le on 2026-11-20 with the default answers to all
twelve decisions: scope L17-0..E, `L:vertex-crude` out, the label-set model M7, the scalar
Fubini route for `L:translated-covariance-CS`, d = 1, 2 in E with d = 3 after Green smoothing,
only true named inputs as fallbacks).  The frozen Lean objects and statement shapes for the item
agents A, B, C, D and E of the pairing-envelope chain.  Nothing in this module proves an item
target.

TeX anchors: main file `notes/notes_stratonovich_ham_second_moment.tex` at revision 0788ddee
(book 1.1.0; the same line numbers at edf7085f, book 1.1.3), read with
`git show 0788ddee:notes/<file>.tex`:
* "Covariance pairings of translated kernels" (`E:translated-covariance-form`): lines
  1156-1185; `L:translated-covariance-CS` statement 1186-1197 (`E:translated-covariance-CS`
  1191-1193), proof 1199-1297;
* the section "A finite product bound for two ordered chains": setup 1434-1488 (edge data
  1436-1444, `E:pairing-edge-norms` 1445-1458, two chains and `E:pairing-diagram-general`
  1460-1475, admissible assignments and `E:pairing-product-general` 1477-1487);
  `L:pairing-product-envelope` statement 1489-1500 (`E:pairing-product-envelope` 1492-1495),
  proof 1502-1639: Step 1 1510-1537 (`E:pairing-convolution-norms`: claim 1522-1535, display
  1524-1530), Step 2 1539-1595, Step 3 1598-1612, Step 4 1615-1627, Step 5 1631-1638;
* consumers (item E): `E:crude-norms` 1970-1976, `L:crude-corrected` 1978-1985, proof
  1987-2054; `P:envelope` 2352-2373, proof 2375-2433.

Model choice M7 (the label-set two-chain model, decision 3): labels of an arbitrary type `α`
with decidable equality; two ordered chains as lists `c1`, `c2` (either may be empty); the
predecessor `p(l)` inside the own chain, `none` (the origin `(0,0)`) at the first vertex; the
matching `D` as a `Finset (Sym2 α)` (an edge keeps its identity when other labels are deleted);
per-edge data `EdgeData` (the set `A_e`, the spectral measure `μ_e`); kernels
`G_l : ℝ → Rd d → ℝ≥0∞` read on positive times; the diagram integral `pairingIntegral` as the
`lmarginal` over the labels of one coordinate `(s_l, x_l) ∈ ℝ × ℝ^d` per label, evaluated at
the base point `0` (the integrand of a well-formed diagram does not depend on the
coordinates outside the labels).  Bridge to M4 (`DiagramModel`): `m4Chain`, `M4BridgeTarget`.

Readings (for the fidelity review):
* everything is in `ℝ≥0∞`; the TeX's finiteness hypotheses (`G_l ∈ L¹`, `N_{1,e}`,
  `N_{2,e} < ∞`, `ν((0,L]) < ∞`, `μ` finite) are explicit hypotheses, so `0 * ∞ = 0` never
  hides a case (TeX 1498-1499: zero kernels, measures and norms are allowed);
* `γ_e(x) = ∫ e^{iξ·x} μ_e(dξ)` is assumed real and nonnegative (`SpecNonneg`); the model
  stores its real part `∫ cos(ξ·x) μ_e(dξ)` (`gammaOf`), equal to the transform under that
  hypothesis (`gammaOf_spec`);
* for nonnegative arguments `Q_L(f,h)` is the lower Lebesgue integral of the nonnegative
  integrand (the complex form of `E:translated-covariance-form` is used only inside item A),
  and `Q = lim_L Q_L` is the supremum over integer caps (`Q_L` increases in `L`);
* `N_{2,e}` is the norm `N_C` of `L:translated-covariance-CS` for `ν = ν_e`, `μ = μ_e`
  (TeX 1514-1515: "The stationary covariance pairing ... has norm `N_{2,e}`"), so its cap is
  `A_e ∩ (0,L]`;
* the finite maximum over `𝒜_D` is the supremum over the admissible assignments `Adm`
  (finite after restricting `ι` to `Q_1 ∪ Q_2`; only `P ≤ sup` and `c · sup = sup (c · ·)` are
  used, as the Step-2 probe shows);
* "finite temporal cap" (Step 1, TeX 1512) is `CappedOn`: every `A_e ⊆ (0, L]` for one `L`;
  a capped edge datum is again an `EdgeData`, so the capped statements need no new objects.

Target statement shapes (`def ... : Prop`, proved by the item agents): `TranslatedCSTarget`
and its capped form `TranslatedCSCappedTarget` (A), `ConvolutionNormsTarget` (B, Step 1), `RegionalHalfBoundTarget` (C, Step 2),
`CappedEnvelopeAt` (D, Steps 3-4, at the finite cap), `PairingEnvelopeTarget` (B Step 5 and D
assembly: the lemma), `M4BridgeTarget` (E).  True named inputs (fallbacks; each is the TeX
claim itself): `ConvolutionNorms` and `RegionalHalfBound`.

Proved here (interface sanity only): `gammaOf_sub_comm`, `kappa_sub_comm`, `edgeWeight_mk`,
`listPred_eq_none_of_notMem_tail`, `listPred_head`, `listPred_cons_cons`, `gammaOf_spec`,
`NC_sq`, `regionIntegral_univ`, `measurable_conv`, `Adm.empty`, `prodP_le_env`, `env_nil`,
`pairingIntegral_nil`, `labels_eq_empty_of_WF`, `envelope_zero` (the case `n = 0`: both sides
are one), `edgeOf_spec`, `edgeOf_eq`, `Adm.ofWF` and `adm_nonempty` (the admissible set of a
well-formed diagram is nonempty), `waveGreen_two_eq` (`WaveGreen`'s `d = 2` measure has the
density `green2`), `mem_labels_m4Chain`, `m4Chain_wf` (M4 pairings give well-formed label-set
diagrams).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.DiagramModel
public import StratonovichHAMSecondMoment.LowAlphaConvolution

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.PairingInterface

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor)
open DiagramModel (Pi2 diagram covEps)
open WaveGreen (waveGreen)

variable {d : ℕ}

/-! ### Kernels, edge data and the covariance functions -/

/-- A kernel `G : (0,∞) × ℝ^d → [0,∞]`, `G t x` (time first).  Values at nonpositive times are
never read by the model: every integral below is over positive times. -/
abbrev Kernel (d : ℕ) : Type := ℝ → Rd d → ℝ≥0∞

/-- The Fourier transform `∫ e^{iξ·x} μ(dξ)` of a measure is real and nonnegative at every `x`
(TeX 1158-1159 and 1437-1438: "`γ(z) = ∫ e^{iξ·z} μ(dξ)` is real and nonnegative"). -/
def SpecNonneg (μ : Measure (Rd d)) : Prop :=
  ∀ x : Rd d, ∃ r : ℝ, 0 ≤ r ∧
    ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) ∂μ = (r : ℂ)

/-- The covariance `γ(x) = ∫ e^{iξ·x} μ(dξ)` as its real part `∫ cos(ξ·x) μ(dξ)` (equal to the
transform under `SpecNonneg`, `gammaOf_spec`), in `ℝ≥0∞`. -/
def gammaOf (μ : Measure (Rd d)) (x : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ ξ, Real.cos (inner ℝ ξ x) ∂μ)

/-- Per-edge data of the section "A finite product bound" (TeX 1436-1444): a measurable
`A_e ⊆ (0,∞)` and a finite positive `μ_e` with real nonnegative transform `γ_e`. -/
structure EdgeData (d : ℕ) where
  /-- The Laplace set `A_e`. -/
  A : Set ℝ
  measurableSet_A : MeasurableSet A
  A_subset : A ⊆ Ioi 0
  /-- The spectral measure `μ_e`. -/
  μ : Measure (Rd d)
  isFiniteMeasure_μ : IsFiniteMeasure μ
  spec_nonneg : SpecNonneg μ

/-- The spectral measure of an edge datum is finite. -/
instance instIsFiniteMeasureEdgeDataμ (E : EdgeData d) : IsFiniteMeasure E.μ :=
  E.isFiniteMeasure_μ

/-- `ν_e(dλ) = Γ(a)⁻¹ 1_{A}(λ) λ^{a-1} dλ` (TeX 1440-1443). -/
def nuE (a : ℝ) (A : Set ℝ) : Measure ℝ :=
  (volume.restrict A).withDensity fun l => ENNReal.ofReal ((Real.Gamma a)⁻¹ * l ^ (a - 1))

/-- `κ_e(t) = ∫ e^{-λ|t|} ν_e(dλ)` (TeX 1442-1443), in `ℝ≥0∞` (`∞` on the diagonal when
`ν_e` is infinite). -/
def kappa (a : ℝ) (E : EdgeData d) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ l, ENNReal.ofReal (Real.exp (-(l * |t|))) ∂nuE a E.A

/-- The capped temporal kernel `κ_L(t) = ∫_{(0,L]} e^{-λ|t|} ν(dλ)` (TeX 1162-1163). -/
def kappaCap (ν : Measure ℝ) (L t : ℝ) : ℝ≥0∞ :=
  ∫⁻ l in Ioc 0 L, ENNReal.ofReal (Real.exp (-(l * |t|))) ∂ν

/-- Capping an edge datum at `L`: `A_e ∩ (0, L]`. -/
def EdgeData.cap (E : EdgeData d) (L : ℝ) : EdgeData d where
  A := E.A ∩ Ioc 0 L
  measurableSet_A := E.measurableSet_A.inter measurableSet_Ioc
  A_subset := fun _ h => E.A_subset h.1
  μ := E.μ
  isFiniteMeasure_μ := E.isFiniteMeasure_μ
  spec_nonneg := E.spec_nonneg

/-- **Finite temporal cap** (Step 1, TeX 1512): every edge of `D` has `A_e ⊆ (0, L]` for one
`L`. -/
def CappedOn {α : Type*} (D : Finset (Sym2 α)) (ed : Sym2 α → EdgeData d) : Prop :=
  ∃ L : ℝ, ∀ e ∈ D, (ed e).A ⊆ Ioc 0 L

/-! ### The norms -/

/-- `N_0(G) = ∫_0^∞ ∫ G(t,x) dx dt` (TeX 1180 and 1448, with 1455). -/
def N0 (G : Kernel d) : ℝ≥0∞ := ∫⁻ t in Ioi 0, ∫⁻ x, G t x

/-- The zero extension `G^0` to nonpositive times (TeX 1177-1178). -/
def zeroExt (G : Kernel d) : Kernel d := fun t x => (Ioi (0 : ℝ)).indicator (fun t => G t x) t

/-- The translate `T_{A,a} f(t,x) = f(t - A, x - a)` (TeX 1183). -/
def transl (A : ℝ) (a : Rd d) (f : Kernel d) : Kernel d := fun t x => f (t - A) (x - a)

/-- `Q_L(f,h)` of `E:translated-covariance-form` (TeX 1166-1170) for nonnegative `f, h`, over the
full time line: `∫∫ f(t,x) h(s,y) κ_L(t-s) γ(x-y)`. -/
def QL (ν : Measure ℝ) (μ : Measure (Rd d)) (L : ℝ) (f h : Kernel d) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × Rd d, ∫⁻ q : ℝ × Rd d,
    f p.1 p.2 * h q.1 q.2 * kappaCap ν L (p.1 - q.1) * gammaOf μ (p.2 - q.2)

/-- `Q(f,h) = lim_{L→∞} Q_L(f,h)` (TeX 1173-1176), the supremum over integer caps. -/
def Q (ν : Measure ℝ) (μ : Measure (Rd d)) (f h : Kernel d) : ℝ≥0∞ :=
  ⨆ L : ℕ, QL ν μ (L : ℝ) f h

/-- `N_C(G) = Q(G^0, G^0)^{1/2}` (TeX 1181). -/
def NC (ν : Measure ℝ) (μ : Measure (Rd d)) (G : Kernel d) : ℝ≥0∞ :=
  Q ν μ (zeroExt G) (zeroExt G) ^ (2⁻¹ : ℝ)

/-- The Laplace-Fourier transform `𝓛G(λ,ξ) = ∫_{t>0} e^{-λt + iξ·x} G(t,x) dt dx`
(TeX 1449-1450, 1455-1456), a Bochner integral of the real values of `G`: the TeX's transform
when the weighted integrand is integrable (sufficient: `G` measurable, `N_0(G) < ∞` and `λ ≥ 0`),
and `0` by Lean's convention otherwise. -/
def lapFour (G : Kernel d) (l : ℝ) (ξ : Rd d) : ℂ :=
  ∫ p in Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)),
    Complex.exp ((-(l * p.1) : ℝ) + Complex.I * (inner ℝ ξ p.2 : ℝ)) * ((G p.1 p.2).toReal : ℂ)

/-- `N_{1,e}(G) = ∫ |𝓛G(λ,ξ)| ν_e(dλ) μ_e(dξ)` (TeX 1449-1450). -/
def N1 (a : ℝ) (E : EdgeData d) (G : Kernel d) : ℝ≥0∞ :=
  ∫⁻ l, ∫⁻ ξ, ‖lapFour G l ξ‖ₑ ∂E.μ ∂nuE a E.A

/-- `N_{2,e}(G)`, the cap limit of `E:pairing-edge-norms` (TeX 1451-1452, 1456-1458): the norm
`N_C` of the stationary covariance pairing with `ν = ν_e`, `μ = μ_e`. -/
def N2 (a : ℝ) (E : EdgeData d) (G : Kernel d) : ℝ≥0∞ := NC (nuE a E.A) E.μ G

/-- The one-sided spacetime convolution `(G*H)(t,x) = ∫_0^t ∫ G(s,y) H(t-s, x-y) dy ds`
(TeX 1522; the fused kernel `F = G_a * G_b` of Step 2, 1563). -/
def conv (G H : Kernel d) : Kernel d :=
  fun t x => ∫⁻ s in Ioo 0 t, ∫⁻ y, G s y * H (t - s) (x - y)

/-! ### The label-set two-chain model (M7) -/

/-- The predecessor of `x` in a list: the element just before it, `none` at the head
(the origin). -/
def listPred {α : Type*} [DecidableEq α] : List α → α → Option α
  | [], _ => none
  | [_], _ => none
  | a :: b :: l, x => if x = b then some a else listPred (b :: l) x

/-- A two-chain diagram on labels `α` (TeX 1460-1463): two ordered chains (either may be empty)
and the matching `D`. -/
structure TwoChain (α : Type*) where
  c1 : List α
  c2 : List α
  D : Finset (Sym2 α)

namespace TwoChain

variable {α : Type*} [DecidableEq α]

/-- The kernel labels `I_1 ∪ I_2`. -/
def labels (dg : TwoChain α) : Finset α := (dg.c1 ++ dg.c2).toFinset

/-- Well formed: distinct labels, and `D` a perfect matching of them (each edge has two
distinct endpoints among the labels, each label lies in exactly one edge). -/
structure WF (dg : TwoChain α) : Prop where
  nodup : (dg.c1 ++ dg.c2).Nodup
  edge : ∀ e ∈ dg.D, ¬ e.IsDiag ∧ ∀ x ∈ e, x ∈ dg.labels
  cover : ∀ l ∈ dg.labels, ∃! e, e ∈ dg.D ∧ l ∈ e

/-- The predecessor `p(l)` in the own chain of `l`, `none` at a first vertex (TeX 1462-1463). -/
def pred (dg : TwoChain α) (l : α) : Option α :=
  if l ∈ dg.c1 then listPred dg.c1 l else listPred dg.c2 l

/-- `s_{p(l)}`, with `0` at a first vertex. -/
def predTime (dg : TwoChain α) (z : α → ℝ × Rd d) (l : α) : ℝ :=
  (dg.pred l).elim 0 fun p => (z p).1

/-- `x_{p(l)}`, with `0` at a first vertex. -/
def predPos (dg : TwoChain α) (z : α → ℝ × Rd d) (l : α) : Rd d :=
  (dg.pred l).elim 0 fun p => (z p).2

/-- The product of the two positive ordered time simplices (TeX 1474-1475), all positions
free: `s_{p(l)} < s_l` for every label (open simplices). -/
def posSimplex (dg : TwoChain α) : Set (α → ℝ × Rd d) :=
  {z | ∀ l ∈ dg.labels, dg.predTime z l < (z l).1}

/-- `v` is the last vertex of one of the two chains. -/
def IsEndpoint (dg : TwoChain α) (v : α) : Prop :=
  dg.c1.getLast? = some v ∨ dg.c2.getLast? = some v

end TwoChain

open TwoChain

variable {α : Type*} [DecidableEq α]

/-- `γ` is even: `γ(x - y) = γ(y - x)` (the cosine is even). -/
theorem gammaOf_sub_comm (μ : Measure (Rd d)) (x y : Rd d) :
    gammaOf μ (x - y) = gammaOf μ (y - x) := by
  unfold gammaOf
  rw [← neg_sub y x]
  simp only [inner_neg_right, Real.cos_neg]

/-- `κ` is even: `κ(s - t) = κ(t - s)`. -/
theorem kappa_sub_comm (a : ℝ) (E : EdgeData d) (s t : ℝ) :
    kappa a E (s - t) = kappa a E (t - s) := by
  unfold kappa; rw [abs_sub_comm]

/-- The edge factor `κ_e(s_j - s_k) γ_e(x_j - x_k)` of `E:pairing-diagram-general`, symmetric in
the endpoints. -/
def edgeWeight (a : ℝ) (E : EdgeData d) (z : α → ℝ × Rd d) : Sym2 α → ℝ≥0∞ :=
  Sym2.lift ⟨fun j k => kappa a E ((z j).1 - (z k).1) * gammaOf E.μ ((z j).2 - (z k).2),
    fun j k => by dsimp only; rw [kappa_sub_comm, gammaOf_sub_comm]⟩

omit [DecidableEq α] in
/-- Unfolding `edgeWeight` at an edge `{j, k}`. -/
theorem edgeWeight_mk (a : ℝ) (E : EdgeData d) (z : α → ℝ × Rd d) (j k : α) :
    edgeWeight a E z s(j, k) = kappa a E ((z j).1 - (z k).1) * gammaOf E.μ ((z j).2 - (z k).2) :=
  rfl

/-- The integrand of `E:pairing-diagram-general` (TeX 1464-1473), restricted to the simplices. -/
def integrand (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d)
    (z : α → ℝ × Rd d) : ℝ≥0∞ :=
  dg.posSimplex.indicator (fun z =>
    (∏ l ∈ dg.labels, G l ((z l).1 - dg.predTime z l) ((z l).2 - dg.predPos z l)) *
      ∏ e ∈ dg.D, edgeWeight a (ed e) z e) z

/-- **`I_D(G)`** (`E:pairing-diagram-general`, TeX 1460-1475): the integral over one coordinate
`(s_l, x_l)` per label, as an `lmarginal`, at the base point `0`. -/
def pairingIntegral (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) :
    ℝ≥0∞ :=
  (∫⋯∫⁻_dg.labels, integrand a dg ed G ∂fun _ => (volume : Measure (ℝ × Rd d))) 0

/-- The diagram integral over a region `R` (Step 2: "on any region", TeX 1547). -/
def regionIntegral (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d)
    (R : Set (α → ℝ × Rd d)) : ℝ≥0∞ :=
  (∫⋯∫⁻_dg.labels, R.indicator (integrand a dg ed G) ∂fun _ => (volume : Measure (ℝ × Rd d))) 0

/-! ### Admissible assignments and the envelope -/

/-- **Admissible `(Q, ι)`** (TeX 1477-1480): `Q_0, Q_1, Q_2` partition the labels `L`,
`|Q_0| = |Q_1|`, and `ι : Q_1 ∪ Q_2 → D` uses each edge once on `Q_1` or twice on `Q_2`, never
both; no incidence requirement. -/
structure Adm (L : Finset α) (D : Finset (Sym2 α)) where
  Q0 : Finset α
  Q1 : Finset α
  Q2 : Finset α
  iota : α → Sym2 α
  cover : Q0 ∪ Q1 ∪ Q2 = L
  d01 : Disjoint Q0 Q1
  d02 : Disjoint Q0 Q2
  d12 : Disjoint Q1 Q2
  card01 : Q0.card = Q1.card
  mapsTo : ∀ l ∈ Q1 ∪ Q2, iota l ∈ D
  edge : ∀ e ∈ D,
    ((Q1.filter fun l => iota l = e).card = 1 ∧ (Q2.filter fun l => iota l = e).card = 0) ∨
    ((Q1.filter fun l => iota l = e).card = 0 ∧ (Q2.filter fun l => iota l = e).card = 2)

/-- `𝒫_{Q,ι}(G)` of `E:pairing-product-general` (TeX 1481-1487). -/
def prodP (a : ℝ) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) {L : Finset α}
    {D : Finset (Sym2 α)} (A : Adm L D) : ℝ≥0∞ :=
  (∏ l ∈ A.Q0, N0 (G l)) * (∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) (G l)) *
    ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) (G l)

/-- **The envelope** `max_{(Q,ι) ∈ 𝒜_D} 𝒫_{Q,ι}(G)`, the right side of
`E:pairing-product-envelope` (TeX 1492-1495), as the supremum over admissible assignments. -/
def env (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) : ℝ≥0∞ :=
  ⨆ A : Adm dg.labels dg.D, prodP a ed G A

/-- The hypotheses of `L:pairing-product-envelope` on the kernels (TeX 1490-1491): measurable,
integrable, and finite first and second norms for every label and every edge of `D`. -/
structure KernelHyp (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) :
    Prop where
  meas : ∀ l ∈ dg.labels, Measurable (Function.uncurry (G l))
  N0_lt : ∀ l ∈ dg.labels, N0 (G l) < ∞
  N1_lt : ∀ l ∈ dg.labels, ∀ e ∈ dg.D, N1 a (ed e) (G l) < ∞
  N2_lt : ∀ l ∈ dg.labels, ∀ e ∈ dg.D, N2 a (ed e) (G l) < ∞

/-! ### Frozen targets -/

/-- **A target, `L:translated-covariance-CS`** (TeX 1186-1197 with the setup 1156-1185 at
revision edf7085f (book 1.1.3)): for `μ` finite with real nonnegative transform and `ν` finite
on every `(0,L]`, nonnegative measurable `G₁, G₂` with `N_0, N_C < ∞` and arbitrary origins,
`0 ≤ Q(T_{A,a}G₁⁰, T_{B,b}G₂⁰) ≤ N_C(G₁) N_C(G₂)` and `Q(T_{A,a}Gᵢ⁰, T_{A,a}Gᵢ⁰) = N_C(Gᵢ)²`. -/
def TranslatedCSTarget (d : ℕ) : Prop :=
  ∀ (ν : Measure ℝ) (μ : Measure (Rd d)), (∀ L : ℝ, 0 < L → ν (Ioc 0 L) < ∞) →
    IsFiniteMeasure μ → SpecNonneg μ →
    ∀ G₁ G₂ : Kernel d, Measurable (Function.uncurry G₁) → Measurable (Function.uncurry G₂) →
      N0 G₁ < ∞ → N0 G₂ < ∞ → NC ν μ G₁ < ∞ → NC ν μ G₂ < ∞ →
      ∀ (A B : ℝ) (x y : Rd d),
        Q ν μ (transl A x (zeroExt G₁)) (transl B y (zeroExt G₂)) ≤ NC ν μ G₁ * NC ν μ G₂ ∧
        Q ν μ (transl A x (zeroExt G₁)) (transl A x (zeroExt G₁)) = NC ν μ G₁ ^ 2 ∧
        Q ν μ (transl A x (zeroExt G₂)) (transl A x (zeroExt G₂)) = NC ν μ G₂ ^ 2

/-- **A target, the capped form** (Steps 1-3 of the proof of `L:translated-covariance-CS`, TeX
1207-1268 at revision edf7085f (book 1.1.3): "This proves the capped form of
`E:translated-covariance-CS`"): at every finite cap `L > 0`, Cauchy-Schwarz for translates and
the common-translation identity, for nonnegative measurable integrable `G₁, G₂`.  The identity is
stated for `G₁`; the `G₂` identity of the TeX's capped form (1262, 1266-1267) is the same
statement with `G₂` in the `G₁` slot, since the target quantifies over both kernels. -/
def TranslatedCSCappedTarget (d : ℕ) : Prop :=
  ∀ (ν : Measure ℝ) (μ : Measure (Rd d)) (L : ℝ), 0 < L → ν (Ioc 0 L) < ∞ →
    IsFiniteMeasure μ → SpecNonneg μ →
    ∀ G₁ G₂ : Kernel d, Measurable (Function.uncurry G₁) → Measurable (Function.uncurry G₂) →
      N0 G₁ < ∞ → N0 G₂ < ∞ →
      ∀ (A B : ℝ) (x y : Rd d),
        QL ν μ L (transl A x (zeroExt G₁)) (transl B y (zeroExt G₂)) ≤
            QL ν μ L (zeroExt G₁) (zeroExt G₁) ^ (2⁻¹ : ℝ) *
              QL ν μ L (zeroExt G₂) (zeroExt G₂) ^ (2⁻¹ : ℝ) ∧
          QL ν μ L (transl A x (zeroExt G₁)) (transl A x (zeroExt G₁)) =
            QL ν μ L (zeroExt G₁) (zeroExt G₁)

/-- **B target, `E:pairing-convolution-norms`** (claim and proof TeX 1522-1535, display
1524-1530, in Step 1 1510-1537, at revision edf7085f (book 1.1.3)): for nonnegative measurable
integrable `G, H` and every edge datum at a finite temporal cap, `N_0(G*H) = N_0(G)N_0(H)`, `N_{1,e}(G*H) ≤ N_0(G)N_{1,e}(H)` and
`N_{2,e}(G*H) ≤ N_0(G)N_{2,e}(H)`. -/
def ConvolutionNormsTarget (d : ℕ) : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 →
    ∀ G H : Kernel d, Measurable (Function.uncurry G) → Measurable (Function.uncurry H) →
      N0 G < ∞ → N0 H < ∞ →
      N0 (conv G H) = N0 G * N0 H ∧
        ∀ E : EdgeData d, (∃ L : ℝ, E.A ⊆ Ioc 0 L) →
          N1 a E (conv G H) ≤ N0 G * N1 a E H ∧ N2 a E (conv G H) ≤ N0 G * N2 a E H

/-- **Named input (fallback for B's Step 1): `E:pairing-convolution-norms`** (TeX 1522-1535,
display 1524-1530, at revision edf7085f (book 1.1.3)), for every exponent and every capped
edge datum.  True (it is the TeX claim); used only if B overruns. -/
structure ConvolutionNorms (d : ℕ) : Prop where
  holds : ConvolutionNormsTarget d

/-- The full bound `I_D(G) ≤ Env_D(G)` at the finite cap for every well-formed diagram with `n`
edges on labels `α`, every capped edge data and every kernel family with the lemma's
hypotheses (Step 2's induction hypothesis "the full bound at `n-1`", TeX 1545, and D's output
before Step 5). -/
def CappedEnvelopeAt (d : ℕ) (α : Type*) [DecidableEq α] (a : ℝ) (n : ℕ) : Prop :=
  ∀ (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d),
    dg.WF → dg.D.card = n → CappedOn dg.D ed → KernelHyp a dg ed G →
      pairingIntegral a dg ed G ≤ env a dg ed G

/-- **C target, the regional half-bound of Step 2** (TeX 1539-1595 at revision edf7085f (book
1.1.3)): assume the full bound at the finite cap for every diagram with `n` edges (all chain
shapes, all kernel families, all edge data).  Let `dg` have `n + 1` edges, `v` an endpoint of a
chain, `w` its partner (`e₀ = {w, v} ∈ D`; TeX's `a`), and `R` a measurable region whose
indicator does not depend on `(s_v, x_v)`, on which `s_w ≤ s_{p(v)}`.  Then the integral over
`R` is at most one half of the envelope. -/
def RegionalHalfBoundTarget (d : ℕ) (α : Type*) [DecidableEq α] (a : ℝ) (n : ℕ) : Prop :=
  0 < a → a < 1 → CappedEnvelopeAt d α a n →
    ∀ (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d),
      dg.WF → dg.D.card = n + 1 → CappedOn dg.D ed → KernelHyp a dg ed G →
      ∀ (v w : α) (R : Set (α → ℝ × Rd d)), dg.IsEndpoint v → s(w, v) ∈ dg.D →
        MeasurableSet R →
        (∀ z z' : α → ℝ × Rd d, (∀ l, l ≠ v → z l = z' l) → (z ∈ R ↔ z' ∈ R)) →
        (∀ z ∈ R, (z w).1 ≤ dg.predTime z v) →
        2 * regionIntegral a dg ed G R ≤ env a dg ed G

/-- **Named input (fallback for C): the regional half-bound** (Step 2, TeX 1539-1595 at
revision edf7085f (book 1.1.3)), for every exponent and every edge count.  True (it is the TeX
claim); used only if C overruns. -/
structure RegionalHalfBound (d : ℕ) (α : Type*) [DecidableEq α] : Prop where
  holds : ∀ (a : ℝ) (n : ℕ), RegionalHalfBoundTarget d α a n

/-- **The lemma's target, `L:pairing-product-envelope`** (`E:pairing-product-envelope`, TeX
1489-1500 at revision edf7085f (book 1.1.3)): for `0 < a < 1`, every well-formed two-chain
diagram, all edge data and all kernels with the lemma's hypotheses,
`I_D(G) ≤ max_{𝒜_D} 𝒫_{Q,ι}(G)`. -/
def PairingEnvelopeTarget (d : ℕ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 →
    ∀ (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d),
      dg.WF → KernelHyp a dg ed G → pairingIntegral a dg ed G ≤ env a dg ed G

/-! ### The bridge to M4 (item E) -/

/-- The smoothed spectral measure `e^{-ε|ξ|²/2} μ(dξ)` (the spectral measure of
`γ_ε = p_ε * Γ`, `LowAlphaConvolution.gammaEps_spectral`; TeX 2013-2018). -/
def smoothSpec (μ : Measure (Rd d)) (ε : ℝ) : Measure (Rd d) :=
  μ.withDensity fun ξ => ENNReal.ofReal (gaussFactor ε ξ)

/-- The damped kernel `e^{-θs} g(s,y)` (TeX 1996-1997). -/
def damp (θ : ℝ) (g : Kernel d) : Kernel d := fun s y => ENNReal.ofReal (Real.exp (-(θ * s))) * g s y

/-- The M4 diagram on the label-set model: chain `I_1 = (0, …, m-1)`, chain
`I_2 = (m, …, m+n-1)` of `Fin (m + n)`, and the edges `{i, D i}`. -/
def m4Chain (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) : TwoChain (Fin (m + n)) where
  c1 := List.ofFn fun j : Fin m => Fin.castAdd n j
  c2 := List.ofFn fun j : Fin n => Fin.natAdd m j
  D := Finset.univ.image fun i => s(i, D i)

/-- **E target, the bridge M4 → `I_D`** (TeX 1993-2033, Step 1 of `L:crude-corrected`):
under `H:homog`, at every noise width `ε > 0` there is an edge datum with `A = (0,∞)` and the
smoothed spectral measure, such that every M4 diagram whose Green family has a density `g`
(d = 1: `green1`; d = 2: `green2`; d = 3 after Green smoothing) is bounded, for every `θ ≥ 0`,
by `e^{2θt}` times the label-set integral of the damped kernels with that edge datum on every
edge and the exponent `a = α₀` (the damping, the Gamma mixture of `|s-r|^{-α₀}`, the Fourier
form of `γ_ε`, and the extension to infinite simplices).

Amended 2026-11-20 by the author's decision (L17 interface amendment 1): the hypothesis
`∀ s x, g s x ≠ ⊤` was added after the measurability of `g`.  Without it the Green measures
`G_s = g(s,·) dy` need not be σ-finite, and Mathlib's `Measure.pi` of non-σ-finite factors need
not be the product density, so the increments-to-positions step is not guaranteed; the densities
used (`green1`, `green2`, and in `d = 3` the Green-smoothed `green3s` for `η > 0`) are finite.
Discharged by `PairingBridge.m4_bridge`. -/
def M4BridgeTarget (d : ℕ) : Prop :=
  ∀ {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}, HomogCovariance d alpha α₀ Γ μ →
    ∀ ε : ℝ, 0 < ε → ∃ E : EdgeData d, E.A = Ioi 0 ∧ E.μ = smoothSpec μ ε ∧
      ∀ (G : ℝ → Measure (Rd d)) (g : Kernel d), Measurable (Function.uncurry g) →
        (∀ s x, g s x ≠ ⊤) → (∀ s, G s = volume.withDensity (g s)) →
        ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
        ∀ t θ : ℝ, 0 < t → 0 ≤ θ →
          diagram G (covEps Γ ε) α₀ m n D t ≤
            ENNReal.ofReal (Real.exp (2 * θ * t)) *
              pairingIntegral α₀ (m4Chain m n D) (fun _ => E) (fun _ => damp θ g)

/-- The `d = 2` wave Green density `G(s,y) = 1_{|y|<s} (2π√(s²-|y|²))⁻¹` (TeX 6127-6131,
`WaveGreen`). -/
def green2 (s : ℝ) (y : Rd 2) : ℝ≥0∞ :=
  (Metric.ball (0 : Rd 2) s).indicator
    (fun x => ENNReal.ofReal ((2 * π * Real.sqrt (s ^ 2 - ‖x‖ ^ 2))⁻¹)) y

/-! ### Sanity lemmas (interface only) -/


section Sanity

/-- Auxiliary: a label outside the tail of a list has no predecessor in it. -/
theorem listPred_eq_none_of_notMem_tail :
    ∀ {l : List α} {x : α}, x ∉ l.tail → listPred l x = none
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: l, x, h => by
    have hb : x ≠ b := fun hb => h (by simp [hb])
    have ht : x ∉ (b :: l).tail := fun hm => h (by simp at hm ⊢; exact Or.inr hm)
    simp only [listPred, hb, ite_false]
    exact listPred_eq_none_of_notMem_tail ht

/-- The first vertex of a chain (without repetitions) has the origin as predecessor. -/
theorem listPred_head {x : α} {l : List α} (h : (x :: l).Nodup) : listPred (x :: l) x = none :=
  listPred_eq_none_of_notMem_tail (by simpa using (List.nodup_cons.1 h).1)

/-- The predecessor of the second vertex is the first. -/
theorem listPred_cons_cons (a b : α) (l : List α) : listPred (a :: b :: l) b = some a := by
  simp [listPred]

/-- `γ` is the transform: under `SpecNonneg`, `gammaOf μ x` is `∫ e^{iξ·x} μ(dξ)`. -/
theorem gammaOf_spec {μ : Measure (Rd d)} [IsFiniteMeasure μ] (h : SpecNonneg μ) (x : Rd d) :
    ((gammaOf μ x).toReal : ℂ) = ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) ∂μ := by
  obtain ⟨r, hr, hint⟩ := h x
  have hmeas : Continuous fun ξ : Rd d => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) := by
    fun_prop
  have hI : Integrable (fun ξ : Rd d => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) μ := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
    intro ξ
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hre := integral_re hI
  have hcos : ∀ ξ : Rd d, RCLike.re (Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) =
      Real.cos (inner ℝ ξ x) := fun ξ => by
    rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re _
  simp only [hcos] at hre
  rw [hint, RCLike.re_to_complex, Complex.ofReal_re] at hre
  rw [hint, gammaOf, hre, ENNReal.toReal_ofReal hr]

/-- `N_C(G)² = Q(G⁰, G⁰)`. -/
theorem NC_sq (ν : Measure ℝ) (μ : Measure (Rd d)) (G : Kernel d) :
    NC ν μ G ^ 2 = Q ν μ (zeroExt G) (zeroExt G) := by
  rw [NC]
  simpa using ENNReal.rpow_inv_natCast_pow (n := 2) two_ne_zero (Q ν μ (zeroExt G) (zeroExt G))

/-- The whole space as a region gives the diagram integral. -/
theorem regionIntegral_univ (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) : regionIntegral a dg ed G univ = pairingIntegral a dg ed G := by
  simp [regionIntegral, pairingIntegral]

/-- Measurability of the fused kernel `G * H`. -/
theorem measurable_conv {G H : Kernel d} (hG : Measurable (Function.uncurry G))
    (hH : Measurable (Function.uncurry H)) : Measurable (Function.uncurry (conv G H)) := by
  have hin : Measurable fun q : ((ℝ × Rd d) × ℝ) × Rd d =>
      G q.1.2 q.2 * H (q.1.1.1 - q.1.2) (q.1.1.2 - q.2) := by
    refine Measurable.mul ?_ ?_
    · exact hG.comp (measurable_fst.snd.prodMk measurable_snd)
    · exact hH.comp ((measurable_fst.fst.fst.sub measurable_fst.snd).prodMk
        (measurable_fst.fst.snd.sub measurable_snd))
  have h1 : Measurable fun p : (ℝ × Rd d) × ℝ =>
      ∫⁻ y, G p.2 y * H (p.1.1 - p.2) (p.1.2 - y) := hin.lintegral_prod_right'
  have hS : MeasurableSet {p : (ℝ × Rd d) × ℝ | 0 < p.2 ∧ p.2 < p.1.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.fst)
  have h2 := (h1.indicator hS).lintegral_prod_right' (ν := (volume : Measure ℝ))
  convert h2 using 1
  ext ⟨t, x⟩
  simp only [Function.uncurry_apply_pair, conv]
  rw [← lintegral_indicator measurableSet_Ioo]
  congr 1

/-! #### Admissible assignments and the empty diagram -/

/-- The empty assignment (the case `n = 0`). -/
def Adm.empty : Adm (∅ : Finset α) (∅ : Finset (Sym2 α)) where
  Q0 := ∅
  Q1 := ∅
  Q2 := ∅
  iota := fun x => s(x, x)
  cover := by simp
  d01 := by simp
  d02 := by simp
  d12 := by simp
  card01 := rfl
  mapsTo := by simp
  edge := by simp

/-- Every admissible product is at most the envelope. -/
theorem prodP_le_env (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d)
    (A : Adm dg.labels dg.D) : prodP a ed G A ≤ env a dg ed G :=
  le_iSup (fun B : Adm dg.labels dg.D => prodP a ed G B) A

/-- `n = 0`: with no labels and no edges the envelope is one (TeX: "For `n = 0`, both
sides are one", 1498-1499). -/
theorem env_nil (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d)
    (hL : dg.labels = ∅) (hD : dg.D = ∅) : env a dg ed G = 1 := by
  have hone : ∀ A : Adm dg.labels dg.D, prodP a ed G A = 1 := by
    intro A
    have hc : A.Q0 ∪ A.Q1 ∪ A.Q2 = ∅ := A.cover.trans hL
    rw [Finset.union_eq_empty, Finset.union_eq_empty] at hc
    simp [prodP, hc.1.1, hc.1.2, hc.2]
  refine le_antisymm (iSup_le fun A => (hone A).le) ?_
  have A0 : Adm dg.labels dg.D := hL ▸ hD ▸ Adm.empty
  exact (hone A0).symm.le.trans (prodP_le_env a dg ed G A0)

/-- `n = 0`: with no labels and no edges the diagram integral is one. -/
theorem pairingIntegral_nil (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) (hL : dg.labels = ∅) (hD : dg.D = ∅) : pairingIntegral a dg ed G = 1 := by
  unfold pairingIntegral
  rw [hL, lmarginal_empty]
  have hmem : (0 : α → ℝ × Rd d) ∈ dg.posSimplex := by
    intro l hl; rw [hL] at hl; simp at hl
  simp only [integrand, Set.indicator_of_mem hmem, hL, hD, Finset.prod_empty, mul_one]

/-- A well-formed diagram without edges has no labels. -/
theorem labels_eq_empty_of_WF {dg : TwoChain α} (hwf : dg.WF) (hD : dg.D = ∅) :
    dg.labels = ∅ := by
  ext l
  simp only [Finset.notMem_empty, iff_false]
  intro hl
  obtain ⟨e, ⟨he, _⟩, _⟩ := hwf.cover l hl
  simp [hD] at he

/-- **The case `n = 0` of `L:pairing-product-envelope`**: both sides are one. -/
theorem envelope_zero (a : ℝ) {dg : TwoChain α} (hwf : dg.WF) (hD : dg.D = ∅)
    (ed : Sym2 α → EdgeData d) (G : α → Kernel d) :
    pairingIntegral a dg ed G = 1 ∧ env a dg ed G = 1 :=
  ⟨pairingIntegral_nil a dg ed G (labels_eq_empty_of_WF hwf hD) hD,
    env_nil a dg ed G (labels_eq_empty_of_WF hwf hD) hD⟩

/-- The edge through a label of a well-formed diagram. -/
def edgeOf {dg : TwoChain α} (hwf : dg.WF) (l : α) : Sym2 α :=
  if h : l ∈ dg.labels then (hwf.cover l h).exists.choose else s(l, l)

theorem edgeOf_spec {dg : TwoChain α} (hwf : dg.WF) {l : α} (h : l ∈ dg.labels) :
    edgeOf hwf l ∈ dg.D ∧ l ∈ edgeOf hwf l := by
  unfold edgeOf; simp only [h, ↓reduceDIte]; exact (hwf.cover l h).exists.choose_spec

theorem edgeOf_eq {dg : TwoChain α} (hwf : dg.WF) {l : α} (h : l ∈ dg.labels) {e : Sym2 α}
    (he : e ∈ dg.D) (hl : l ∈ e) : edgeOf hwf l = e :=
  (hwf.cover l h).unique (edgeOf_spec hwf h) ⟨he, hl⟩

/-- **The admissible set of a well-formed diagram is nonempty** (TeX 1480): every label in
`Q_2`, mapped to its own edge (each edge used twice). -/
def Adm.ofWF {dg : TwoChain α} (hwf : dg.WF) : Adm dg.labels dg.D where
  Q0 := ∅
  Q1 := ∅
  Q2 := dg.labels
  iota := edgeOf hwf
  cover := by simp
  d01 := by simp
  d02 := by simp
  d12 := by simp
  card01 := rfl
  mapsTo := fun l hl => (edgeOf_spec hwf (by simpa using hl)).1
  edge := by
    intro e he
    right
    refine ⟨by simp, ?_⟩
    induction e using Sym2.ind with
    | h j k =>
      have hjk : j ≠ k := fun h => (hwf.edge _ he).1 (Sym2.mk_isDiag_iff.2 h)
      have hf : (dg.labels.filter fun l => edgeOf hwf l = s(j, k)) = {j, k} := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hl, hle⟩
          have := (edgeOf_spec hwf hl).2
          rw [hle] at this
          exact Sym2.mem_iff.1 this
        · intro hl'
          have hlm : l ∈ s(j, k) := Sym2.mem_iff.2 hl'
          have hlL : l ∈ dg.labels := (hwf.edge _ he).2 l hlm
          exact ⟨hlL, edgeOf_eq hwf hlL he hlm⟩
      rw [hf, Finset.card_pair hjk]

theorem adm_nonempty {dg : TwoChain α} (hwf : dg.WF) : Nonempty (Adm dg.labels dg.D) :=
  ⟨Adm.ofWF hwf⟩

/-! #### The `d = 2` Green density and the M4 chains -/

/-- **`WaveGreen`'s `d = 2` measure has the density `green2`** (definitional). -/
theorem waveGreen_two_eq (s : ℝ) : waveGreen 2 s = volume.withDensity (green2 s) := rfl

/-- Every label of `Fin (m + n)` lies on one of the two M4 chains. -/
theorem mem_labels_m4Chain {m n : ℕ} (D : Fin (m + n) → Fin (m + n)) (i : Fin (m + n)) :
    i ∈ (m4Chain m n D).labels := by
  simp only [TwoChain.labels, m4Chain, List.mem_toFinset, List.mem_append, List.mem_ofFn]
  by_cases h : (i : ℕ) < m
  · exact Or.inl ⟨⟨i, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨(i : ℕ) - m, by omega⟩, Fin.ext ?_⟩
    simp only [Fin.natAdd]
    omega

/-- **The M4 diagram of a pairing is well formed** on the label-set model. -/
theorem m4Chain_wf {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) :
    (m4Chain m n D).WF := by
  rw [DiagramModel.mem_Pi2] at hD
  refine ⟨?_, ?_, ?_⟩
  · simp only [m4Chain]
    refine List.nodup_append.2 ⟨List.nodup_ofFn.2 ?_, List.nodup_ofFn.2 ?_, ?_⟩
    · intro x y hxy; exact Fin.ext (by simpa using congrArg Fin.val hxy)
    · intro x y hxy; exact Fin.ext (by simpa using congrArg Fin.val hxy)
    · intro x hx y hy hxy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
      have := congrArg Fin.val hxy
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
  · intro e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
    exact ⟨fun h => (hD i).1 (Sym2.mk_isDiag_iff.1 h).symm,
      fun x _ => mem_labels_m4Chain D x⟩
  · intro l _
    refine ⟨s(l, D l), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ l), Sym2.mem_mk_left l _⟩,
      fun e ⟨he, hle⟩ => ?_⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
    rcases Sym2.mem_iff.1 hle with rfl | rfl
    · rfl
    · rw [(hD i).2, Sym2.eq_swap]

end Sanity

end StratonovichHAMSecondMoment.PairingInterface
