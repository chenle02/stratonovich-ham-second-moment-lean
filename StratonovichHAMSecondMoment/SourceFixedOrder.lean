module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item D (first half): the `L²` construction of `L:joint-fixed-order`
(TeX lines 1853-1862, proof Step 4 1949-1965 at revision edf7085f (book 1.1.3)).

Statement proved (`fixed_order_l2`, the frozen `FixedOrderL2Target` of `SourceInterface`): under
`H:homog`, for every source field (`SourceField`), `n ≥ 1`, `t > 0` and `x`, the chain integral
`Y_n^a(t,x)` (`Yw`, at real vertexwise widths `(ε, δ)`) converges in `L²(Ω)` as all `2n` widths
tend to zero at arbitrary relative rates (`widthFilter n ×ˢ widthFilter n`), and the limit is
`S_n(g_n)(t,x)` (`stratInt`, the limit at common noise widths, which therefore exists).

Hypothesis: C's headline `TerminalMixedMomentTarget d` (the mixed moments at positive widths are
M8 diagram sums after the chain reversal, TeX 858-905 and 1951-1953), taken with exactly its
frozen signature and discharged at integration.

Route (TeX Step 4, 1949-1965): `E[Y^a Y^b] = Σ_{D ∈ Π_n} F_{ε∘ρ, δ∘ρ, D}(t,t)` (C); the reversed
concatenation `(ε^a, ε^b) ↦ (ε^a ++ ε^b) ∘ ρ` sends the product of the width filters into
`widthFilter (n + n)` (`tendsto_revApp`), so by L18's joint diagram limit
(`WickFinal.joint_diagram_limit_l18`) every mixed moment, including either diagonal one, tends
to one finite sum `Q_n`; hence `‖Y^a - Y^b‖² → Q_n + Q_n - 2Q_n = 0` (1956-1959), the family is
Cauchy along the joint width filter, and completeness of `L²` gives the limit (1960).
Restricting to common widths (the constant-vector map, `tendsto_const_widthFilter`) gives the
common-width limit, which is `stratInt` by `Tendsto.limUnder_eq` (1963-1964).  The
identification of the limit `Q_n` with M4's diagram limits (E's `DiagramLimIdentTarget`) is not
needed here.  The Green-before-noise sentence (1960-1963) is `SourceGreenFirst.green_first`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SourceInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.SourceFixedOrder

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open WickInterface (capDom wickF widthFilter posOrthant)
open DiagramModel (Pi2 rev)
open SourceInterface

/-! ### Width vectors: reversed concatenation and filters -/

/-- The reversed concatenation `(u ++ v) ∘ ρ` of two width vectors of order `n`
(`ρ = DiagramModel.rev n n`, the chain reversal of `P:mixed` Step 2, TeX 888-905). -/
def revApp {n : ℕ} (u v : Fin n → ℝ) : Fin (n + n) → ℝ :=
  fun i => Fin.append u v (rev n n i)

/-- A concatenation of two positive vectors is positive. -/
theorem append_pos {m n : ℕ} {u : Fin m → ℝ} {v : Fin n → ℝ} (hu : ∀ j, 0 < u j)
    (hv : ∀ j, 0 < v j) (k : Fin (m + n)) : 0 < Fin.append u v k := by
  refine Fin.addCases (motive := fun k => 0 < Fin.append u v k) (fun j => ?_) (fun j => ?_) k
  · rw [Fin.append_left]; exact hu j
  · rw [Fin.append_right]; exact hv j

/-- Every coordinate of a concatenation of two vectors tending to `0` tends to `0`. -/
theorem tendsto_append_apply {ι : Type*} {l : Filter ι} {m n : ℕ} {u : ι → Fin m → ℝ}
    {v : ι → Fin n → ℝ} (hu : Tendsto u l (𝓝 0)) (hv : Tendsto v l (𝓝 0)) (k : Fin (m + n)) :
    Tendsto (fun x => Fin.append (u x) (v x) k) l (𝓝 0) := by
  refine Fin.addCases (motive := fun k => Tendsto (fun x => Fin.append (u x) (v x) k) l (𝓝 0))
    (fun j => ?_) (fun j => ?_) k
  · simp only [Fin.append_left]
    exact (tendsto_pi_nhds.1 hu) j
  · simp only [Fin.append_right]
    exact (tendsto_pi_nhds.1 hv) j

/-- The reversed concatenation sends two width-filter limits into the width filter of order
`n + n` (a permutation of coordinates of `Fin.append`). -/
theorem tendsto_revApp {ι : Type*} {l : Filter ι} {n : ℕ} {u v : ι → Fin n → ℝ}
    (hu : Tendsto u l (widthFilter n)) (hv : Tendsto v l (widthFilter n)) :
    Tendsto (fun x => revApp (u x) (v x)) l (widthFilter (n + n)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact tendsto_pi_nhds.2 fun i =>
      tendsto_append_apply (hu.mono_right nhdsWithin_le_nhds)
        (hv.mono_right nhdsWithin_le_nhds) (rev n n i)
  · filter_upwards [hu.eventually (JointFixedOrder.eventually_pos_of_widthFilter n),
      hv.eventually (JointFixedOrder.eventually_pos_of_widthFilter n)] with x h1 h2
    exact fun i _ => append_pos h1 h2 (rev n n i)

/-- The constant-vector map `ε ↦ (ε, …, ε)` sends `𝓝[>] 0` into the width filter (common
noise widths, TeX 1963-1964). -/
theorem tendsto_const_widthFilter (N : ℕ) :
    Tendsto (fun ε : ℝ => fun _ : Fin N => ε) (𝓝[>] 0) (widthFilter N) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (tendsto_pi_nhds.2 fun _ => tendsto_id).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fun _ _ => (show (0 : ℝ) < ε from hε)

/-- The spatial parts of a concatenation of width pairs. -/
theorem append_eps {m n : ℕ} (a : Fin m → PosW) (b : Fin n → PosW) (k : Fin (m + n)) :
    (Fin.append a b k).eps = Fin.append (fun j => (a j).eps) (fun j => (b j).eps) k := by
  refine Fin.addCases (motive := fun k =>
    (Fin.append a b k).eps = Fin.append (fun j => (a j).eps) (fun j => (b j).eps) k)
    (fun j => ?_) (fun j => ?_) k
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

/-- The temporal parts of a concatenation of width pairs. -/
theorem append_del {m n : ℕ} (a : Fin m → PosW) (b : Fin n → PosW) (k : Fin (m + n)) :
    (Fin.append a b k).del = Fin.append (fun j => (a j).del) (fun j => (b j).del) k := by
  refine Fin.addCases (motive := fun k =>
    (Fin.append a b k).del = Fin.append (fun j => (a j).del) (fun j => (b j).del) k)
    (fun j => ?_) (fun j => ?_) k
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

/-- Along the product of the joint width filters, the reversed widths of C's headline are the
reversed concatenations of the real width vectors (`eventually_posW`). -/
theorem eventually_revWidths (n : ℕ) :
    ∀ᶠ pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) in
      (widthFilter n ×ˢ widthFilter n) ×ˢ (widthFilter n ×ˢ widthFilter n),
      (fun i => epsV (posW pq.1.1 pq.1.2) (posW pq.2.1 pq.2.2) (rev n n i)) =
          revApp pq.1.1 pq.2.1 ∧
        (fun i => delV (posW pq.1.1 pq.1.2) (posW pq.2.1 pq.2.2) (rev n n i)) =
          revApp pq.1.2 pq.2.2 := by
  filter_upwards [tendsto_fst.eventually (eventually_posW n),
    tendsto_snd.eventually (eventually_posW n)] with pq h1 h2
  have e1 : (fun j => (posW pq.1.1 pq.1.2 j).eps) = pq.1.1 := funext fun j => (h1 j).1
  have e2 : (fun j => (posW pq.2.1 pq.2.2 j).eps) = pq.2.1 := funext fun j => (h2 j).1
  have e3 : (fun j => (posW pq.1.1 pq.1.2 j).del) = pq.1.2 := funext fun j => (h1 j).2
  have e4 : (fun j => (posW pq.2.1 pq.2.2 j).del) = pq.2.2 := funext fun j => (h2 j).2
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · simp only [epsV, revApp]
    rw [append_eps, e1, e2]
  · simp only [delV, revApp]
    rw [append_del, e3, e4]

/-! ### The joint `L²` limit (Step 4) -/

/-- A finite sum of convergent families converges (existential form). -/
theorem exists_tendsto_finset_sum {ι X : Type*} {l : Filter X} (s : Finset ι)
    {f : ι → X → ℝ} (h : ∀ i ∈ s, ∃ c : ℝ, Tendsto (f i) l (𝓝 c)) :
    ∃ L : ℝ, Tendsto (fun x => ∑ i ∈ s, f i x) l (𝓝 L) := by
  choose! c hc using h
  exact ⟨∑ i ∈ s, c i, tendsto_finsetSum s hc⟩

section Joint

variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- **Step 4, the Gram limit** (TeX 1951-1956 at revision edf7085f (book 1.1.3)): every mixed
moment `E[Y_n^a Y_n^b]` tends to one finite limit `Q_n` as all `4n` widths of the two copies
tend to zero jointly.  Route: C's headline (hypothesis `hM`) writes the mixed moment as
`Σ_D F_{(ε^a++ε^b)∘ρ, (δ^a++δ^b)∘ρ, D}(t,t)`; each diagram has a finite joint limit
(`WickFinal.joint_diagram_limit_l18`, `L:joint-fixed-order` first sentence) along the image of
the reversed concatenation (`tendsto_revApp`). -/
theorem exists_gram_limit (hM : TerminalMixedMomentTarget.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) {t : ℝ}
    (ht : 0 < t) (x : Rd d) {n : ℕ} (hn : 1 ≤ n) :
    ∃ L : ℝ, Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        inner ℝ (Yw hW t ht.le x pq.1.1 pq.1.2) (Yw hW t ht.le x pq.2.1 pq.2.2))
      ((widthFilter n ×ˢ widthFilter n) ×ˢ (widthFilter n ×ˢ widthFilter n)) (𝓝 L) := by
  set F := widthFilter n ×ˢ widthFilter n with hF
  have hψε : Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      revApp pq.1.1 pq.2.1) (F ×ˢ F) (widthFilter (n + n)) :=
    tendsto_revApp (u := fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      pq.1.1) (v := fun pq => pq.2.1) (tendsto_fst.comp tendsto_fst)
      (tendsto_fst.comp tendsto_snd)
  have hψδ : Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      revApp pq.1.2 pq.2.2) (F ×ˢ F) (widthFilter (n + n)) :=
    tendsto_revApp (u := fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      pq.1.2) (v := fun pq => pq.2.2) (tendsto_snd.comp tendsto_fst)
      (tendsto_snd.comp tendsto_snd)
  have hDl : ∀ D ∈ Pi2 n n, ∃ c : ℝ,
      Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (wickF (waveGreen d) Γ α₀ (capDom (revApp pq.1.2 pq.2.2))
          (revApp pq.1.1 pq.2.1) n D t t).toReal) (F ×ˢ F) (𝓝 c) := by
    intro D hD
    obtain ⟨b, hb, hT⟩ :=
      WickFinal.joint_diagram_limit_l18 d hH n n n (two_mul n).symm hn D hD t ht
    -- composites stated through `Tendsto.congr` (a direct expected type times out in `isDefEq`)
    have h2 := (ENNReal.tendsto_toReal hb).comp (hT.comp (hψε.prodMk hψδ))
    exact ⟨b.toReal, h2.congr fun pq => rfl⟩
  obtain ⟨L, hL⟩ := exists_tendsto_finset_sum (l := F ×ˢ F) (Pi2 n n) hDl
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [eventually_revWidths n] with pq hpq
  have hm := (hM hH P W hW t ht x n n (posW pq.1.1 pq.1.2) (posW pq.2.1 pq.2.2)).2
  rw [hpq.1, hpq.2] at hm
  have e : inner ℝ (Yw hW t ht.le x pq.1.1 pq.1.2) (Yw hW t ht.le x pq.2.1 pq.2.2) =
      ∫ ω, Ya hW t ht.le x (posW pq.1.1 pq.1.2) ω * Ya hW t ht.le x (posW pq.2.1 pq.2.2) ω ∂P :=
    (UniformSeriesTail.integral_mul_eq_inner _ _).symm
  rw [e, hm]

/-- **Step 4, `‖Y_n^a - Y_n^b‖₂ → 0`** (TeX 1956-1959 at revision edf7085f (book 1.1.3)):
`‖Y^a - Y^b‖² = E[Y^aY^a] - 2E[Y^aY^b] + E[Y^bY^b] → Q_n - 2Q_n + Q_n = 0`. -/
theorem tendsto_norm_sub (hM : TerminalMixedMomentTarget.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) {t : ℝ}
    (ht : 0 < t) (x : Rd d) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        ‖Yw hW t ht.le x pq.1.1 pq.1.2 - Yw hW t ht.le x pq.2.1 pq.2.2‖)
      ((widthFilter n ×ˢ widthFilter n) ×ˢ (widthFilter n ×ˢ widthFilter n)) (𝓝 0) := by
  set F := widthFilter n ×ˢ widthFilter n with hF
  obtain ⟨L, hL⟩ := exists_gram_limit hM hH P W hW ht x hn
  have h11 : Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      (pq.1, pq.1)) (F ×ˢ F) (F ×ˢ F) := tendsto_fst.prodMk tendsto_fst
  have h22 : Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      (pq.2, pq.2)) (F ×ˢ F) (F ×ˢ F) := tendsto_snd.prodMk tendsto_snd
  have hsq := ((hL.comp h11).sub (hL.const_mul 2)).add (hL.comp h22)
  rw [show L - 2 * L + L = 0 by ring] at hsq
  have hsq' : Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      ‖Yw hW t ht.le x pq.1.1 pq.1.2 - Yw hW t ht.le x pq.2.1 pq.2.2‖ ^ 2) (F ×ˢ F) (𝓝 0) := by
    refine hsq.congr' (Eventually.of_forall fun pq => ?_)
    simp only [Function.comp_apply]
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hs := hsq'.sqrt
  rw [Real.sqrt_zero] at hs
  refine hs.congr' (Eventually.of_forall fun pq => ?_)
  exact Real.sqrt_sq (norm_nonneg _)

end Joint

/-- **`L:joint-fixed-order`, the `L²` half** (`FixedOrderL2Target`; TeX lines 1858-1860, proof
Step 4 1949-1965 at revision edf7085f (book 1.1.3)), with C's headline
`TerminalMixedMomentTarget` as hypothesis: for every source field, `n ≥ 1`, `t > 0` and `x`,
`Y_n^a(t,x)` has a joint `L²` limit as all `2n` vertexwise widths tend to zero at arbitrary
relative rates (Cauchy by `tendsto_norm_sub`, completeness of `L²`), and the limit is the
common-width limit `S_n(g_n)(t,x)` (`stratInt`), which therefore exists.  Uniqueness is
`tendsto_unique_widths`. -/
theorem fixed_order_l2 (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d) :
    FixedOrderL2Target.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x n hn
  set F := widthFilter n ×ˢ widthFilter n with hF
  set Y : (Fin n → ℝ) × (Fin n → ℝ) → Lp ℝ 2 P := fun p => Yw hW t ht.le x p.1 p.2 with hY
  have hcau : Cauchy (map Y F) := by
    rw [cauchy_map_iff]
    refine ⟨inferInstance, ?_⟩
    rw [tendsto_uniformity_iff_dist_tendsto_zero]
    simpa only [dist_eq_norm] using tendsto_norm_sub hM hH P W hW ht x hn
  obtain ⟨X, hX⟩ := cauchy_map_iff_exists_tendsto.1 hcau
  have hconst : Tendsto (fun p : ℝ × ℝ => ((fun _ : Fin n => p.1), (fun _ : Fin n => p.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) F :=
    ((tendsto_const_widthFilter n).comp tendsto_fst).prodMk
      ((tendsto_const_widthFilter n).comp tendsto_snd)
  have hX2 : Tendsto (Ycom hW t ht.le x n) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 X) :=
    (hX.comp hconst).congr fun p => rfl
  have hS : stratInt hW t ht.le x n = X := hX2.limUnder_eq
  rw [hS]
  exact ⟨hX, hX2⟩

end StratonovichHAMSecondMoment.SourceFixedOrder
