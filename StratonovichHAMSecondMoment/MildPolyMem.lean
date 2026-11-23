module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item L20-B (approved by Le on 2026-11-22 with the default answers to all thirteen
decisions): `PolyMemTarget` (`MildInterface`), the membership half of Step 1 of the proof of
`P:mild-construction`, TeX lines 2183-2185 at revision edf7085f (book 1.1.3): "The fixed-width
terminal integrals lie in this space, by their Bochner construction; their fixed-order `L²`
limits `X_n` do too."

Route (the interface's, no difference from the TeX):
* `Y_n^a(t,x)` (`Ya`) is the Bochner integral of `prodL2 hW (attach a z)`, a product of `n` field
  values, hence in the closed subspace `PolyLE hW n`; a Bochner integral of a function with values
  in a closed submodule of a Banach space lies in it (`integral_mem_of_isClosed`, through the
  linear isometry `Submodule.subtypeₗᵢ` of the complete subspace; no integrability needed, the
  junk value `0` also lies in the submodule);
* `X_0 = Y_0` is the case `n = 0` (definitional, `XL2_zero`);
* `X_{n+1} = S_{n+1}(g_{n+1})` (`stratInt`, a `limUnder`): for `t > 0` it is the `L²` limit of
  the common-width `Y_{n+1}` (`SourceFinal.fixed_order_l2_l19`, second clause), each in the closed
  set `PolyLE hW (n+1)`; for `t = 0` the chain measure of order `n + 1 ≥ 1` is the zero measure
  (mass `0^{2(n+1)}/(2(n+1))! = 0`, `TerminalWick.chainMassReal_eq`, any `d`), so the common-width
  family is constantly `0` and its `limUnder` is `0` (TeX 2210: "at `t = 0` the positive orders
  vanish").

Also proved (the proposal's "u partial sums, products" for B; no new frozen name): the partial
sums `U_N = Σ_{n ≤ N} X_n` lie in `PolyLE hW N` (`partialSum_mem`), and, given item A's target as
a hypothesis, the products `W_a · X_n`, `W_a · U_N` are in `L²` with the bound
`E:occupied-multiplication` (`occupied_XL2`, `occupied_partialSum`; TeX 2187-2191).

No `sorry`, no axiom, no instance declared.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.MildPolyMem

universe u

open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open SourceInterface
open MildInterface

/-- A Bochner integral of a function with values in a closed submodule of a real Banach space
lies in that submodule (for any measure; the junk value `0` of a non-integrable function also
lies in it). -/
theorem integral_mem_of_isClosed {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (K : Submodule ℝ E)
    (hK : IsClosed (K : Set E)) {f : α → E} (hf : ∀ a, f a ∈ K) : ∫ a, f a ∂μ ∈ K := by
  have : CompleteSpace K := hK.completeSpace_coe
  let g : α → K := fun a => ⟨f a, hf a⟩
  have hfg : (fun a => f a) = fun a => K.subtypeₗᵢ (g a) := rfl
  rw [hfg, LinearIsometry.integral_comp_comm]
  exact (∫ a, g a ∂μ).2

/-- `PolyLE hW n` is closed. -/
theorem isClosed_PolyLE {X : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : X → Ω → ℝ} {K : X → X → ℝ} (hW : CenteredGaussianField W K P) (n : ℕ) :
    IsClosed (PolyLE hW n : Set (Lp ℝ 2 P)) :=
  Submodule.isClosed_topologicalClosure _

section Members

variable {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- **The fixed-width terminal integrals lie in `P_(<=n)`** (TeX 2183-2184 at revision edf7085f
(book 1.1.3), "by their Bochner construction"): `Y_n^a(t,x) ∈ PolyLE hW n` for every `t ≥ 0`. -/
theorem Ya_mem (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {n : ℕ}
    (a : Fin n → PosW) : Ya hW t ht x a ∈ PolyLE hW n :=
  integral_mem_of_isClosed _ (isClosed_PolyLE hW n)
    fun z => prodL2_mem_PolyLE hW le_rfl (attach a z)

/-- At `t = 0` the terminal chain measure of positive order is zero (order `n + 1`, mass
`0^{2(n+1)}/(2(n+1))! = 0`; the mass `t^{2n}/(2n)!` of order `n` is TeX 1651). -/
theorem chainMeasure_zero_time (x : Rd d) (n : ℕ) :
    chainMeasure d (n + 1) 0 le_rfl x = 0 := by
  refine Measure.measure_univ_eq_zero.mp ?_
  rw [TerminalWickInputs.chainMeasure_univ_eq, TerminalWickInputs.chainMeasureRaw_univ_eq,
    TerminalWick.chainMassReal_eq (n + 1) 0 le_rfl]
  simp

/-- At `t = 0`, `X_{n+1} = S_{n+1}(g_{n+1}) = 0` (TeX 2210: the positive orders vanish). -/
theorem stratInt_zero_time (hW : SourceField α₀ Γ P W) (x : Rd d) (n : ℕ) :
    stratInt hW 0 le_rfl x (n + 1) = 0 := by
  have hY : Ycom hW 0 le_rfl x (n + 1) = fun _ => 0 := by
    funext p
    simp only [Ycom, Yw, Ya, chainMeasure_zero_time x n, integral_zero_measure]
  unfold stratInt
  rw [hY]
  exact tendsto_const_nhds.limUnder_eq

/-- **The fixed-order `L²` limits lie in `P_(<=n)`** (TeX 2184-2185 at revision edf7085f (book
1.1.3), "their fixed-order `L²` limits `X_n` do too"): `X_n(t,x) ∈ PolyLE hW n` for every
`t ≥ 0` (for `n ≥ 1` and `t > 0` from `fixed_order_l2_l19`; at `t = 0` it is `0`). -/
theorem XL2_mem {alpha : ℝ} {μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    [IsProbabilityMeasure P] (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d)
    (n : ℕ) : XL2 hW t ht x n ∈ PolyLE hW n := by
  cases n with
  | zero => exact Ya_mem hW t ht x _
  | succ n =>
    rw [XL2_succ]
    rcases ht.lt_or_eq with htp | rfl
    · have hlim := (SourceFinal.fixed_order_l2_l19 d hH P W hW t htp x (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))).2
      exact (isClosed_PolyLE hW (n + 1)).mem_of_tendsto hlim
        (Eventually.of_forall fun p => Ya_mem hW t htp.le x _)
    · rw [stratInt_zero_time hW x n]
      exact Submodule.zero_mem _

/-- The partial sums `U_N(t,x) = Σ_{n ≤ N} X_n(t,x)` of `u` lie in `PolyLE hW N` (TeX 2181-2183
with `PolyLE_mono`; the partial sums of `u` in Step 6, 2318-2320). -/
theorem partialSum_mem {alpha : ℝ} {μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    [IsProbabilityMeasure P] (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d)
    (N : ℕ) : ∑ n ∈ Finset.range (N + 1), XL2 hW t ht x n ∈ PolyLE hW N :=
  Submodule.sum_mem _ fun n hn =>
    PolyLE_mono hW (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) (XL2_mem hH hW t ht x n)

end Members

/-- **Item B target** (`PolyMemTarget`, TeX 2181-2185 at revision edf7085f (book 1.1.3)): every
`Y_n^a(t,x)` and `X_n(t,x)` lies in `P_(<=n)`, for every `t ≥ 0`. -/
theorem poly_mem (d : ℕ) : PolyMemTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x n
  exact ⟨fun a => Ya_mem hW t ht x a, XL2_mem hH hW t ht x n⟩

section Products

variable {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}

/-- Products with a field value (given item A's target, TeX 2189-2191 `E:occupied-multiplication`):
`W(z) X_n(t,x) ∈ L²` with `‖W(z) X_n‖ ≤ 2√(n+1) ‖W(z)‖ ‖X_n‖`. -/
theorem occupied_XL2 (hA : OccupiedMultTarget.{u, 0}) {alpha : ℝ} {μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) (z : SrcPt d) (t : ℝ)
    (ht : 0 ≤ t) (x : Rd d) (n : ℕ) :
    MemLp (fun ω => fieldL2 hW z ω * XL2 hW t ht x n ω) 2 P ∧
      ‖mulL2 (fieldL2 hW z) (XL2 hW t ht x n)‖ ≤
        2 * Real.sqrt ((n : ℝ) + 1) * ‖fieldL2 hW z‖ * ‖XL2 hW t ht x n‖ :=
  (hA P W (srcCov α₀ Γ) hW).1 n _ (fieldL2_mem_LinG hW z) _ (XL2_mem hH hW t ht x n)

/-- Products of a field value with the partial sums of `u` (given item A's target; TeX 2187-2191
with Step 6, 2318-2320): `W(z) U_N(t,x) ∈ L²` with the bound `2√(N+1) ‖W(z)‖ ‖U_N‖`. -/
theorem occupied_partialSum (hA : OccupiedMultTarget.{u, 0}) {alpha : ℝ} {μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) (z : SrcPt d) (t : ℝ)
    (ht : 0 ≤ t) (x : Rd d) (N : ℕ) :
    MemLp (fun ω => fieldL2 hW z ω * (∑ n ∈ Finset.range (N + 1), XL2 hW t ht x n) ω) 2 P ∧
      ‖mulL2 (fieldL2 hW z) (∑ n ∈ Finset.range (N + 1), XL2 hW t ht x n)‖ ≤
        2 * Real.sqrt ((N : ℝ) + 1) * ‖fieldL2 hW z‖ *
          ‖∑ n ∈ Finset.range (N + 1), XL2 hW t ht x n‖ :=
  (hA P W (srcCov α₀ Γ) hW).1 N _ (fieldL2_mem_LinG hW z) _ (partialSum_mem hH hW t ht x N)

end Products

end StratonovichHAMSecondMoment.MildPolyMem
