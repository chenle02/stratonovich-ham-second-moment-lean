module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L11, item K4: two of the inputs that `TerminalWick` (wave L8-f) left supplied in
`L:terminal-wick` (The finite terminal-chain Wick formula) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f: the terminal-chain
measure `E:terminal-chain-measure` (lines 4275-4288), the statement (lines 4291-4336) and
the proof (lines 4338-4410).

Formalized:
* (i) Strong measurability of the product in `L²` (TeX lines 4357-4359: "Mean-square
  continuity of Gaussian variables implies their continuity in every fixed finite `L^p`.
  Hence, the product is strongly measurable in `L²` on the stated pieces").  The field value
  `W(p)` as an element of `L²` (`fieldL2`) is continuous at every point where the field is
  mean-square continuous (`continuousAt_fieldL2`); the chain product `z ↦ prodL2 hW z` is
  continuous at every tuple whose points are such points (`continuousAt_prodL2`), through the
  Wick formula `‖∏W(z) - ∏W(z₀)‖₂² = F(z,z) - 2F(z,z₀) + F(z₀,z₀)` with `F` a pairing sum of
  inner products (`norm_sub_prodL2_sq`).  From the cell continuity of the lemma
  (`TerminalWick.MeanSquareCellContinuous`) and the absence of time atoms of the chain
  measures (`TimeAtomless`, true for `g_n^{T,x}` because their time marginal has a density),
  the product is a.e. strongly measurable for every chain measure
  (`aestronglyMeasurable_prodL2_of_cell`).
* Measurability of the pairing integrands without measurability of `K`: the hypothesis `hK`
  of `TerminalWick.terminal_wick_paper` (`K` jointly measurable) is not implied by the TeX's
  assumptions (a field can be non-measurable on a cut-time slice).  Under the cell continuity,
  `K(p,q) = ⟪W(p), W(q)⟫` is continuous at pairs of continuity points, so each pairing
  integrand is continuous off a `ν_m ⊗ ν_n`-null set (`aestronglyMeasurable_pairWeight_of_cell`,
  `integrable_pairWeight_of_cell`), and `E:terminal-wick-formula` holds without `hK`
  (`mixed_moment_eq_sum_pairings_of_cell`).  Wrapper `terminal_wick_paper_measurable`:
  `TerminalWick.terminal_wick_paper` without `hmeas` and without `hK`, the cell continuity
  now used.
* (iii) The terminal-chain measures `g_n^{T,x}` of `E:terminal-chain-measure`, constructed:
  `chainMeasureRaw d n T x` on `n`-tuples of points of `ℝ × ℝ^d`, and its image
  `chainMeasure d n T hT x` on `n`-tuples of points of `[0,T] × ℝ^d` (`TerminalWick.Pt`).
  The construction is the pushforward of `(ordered-simplex density in time) ⊗ G_1^{⊗n}` under
  `(s, v) ↦ (s_j, x - Σ_{l ≥ j} (s_{l+1} - s_l) v_l)_j`, which avoids the measurability of
  `h ↦ G_h` as a measure-valued map, using the scaling `G_h(hA) = h G_1(A)`
  (`WaveGreen.waveGreen_scaling`).  `chainMeasureRaw_apply` proves that it IS the TeX's
  measure: for measurable `A`,
  `g_n^{T,x}(A) = ∫_{0<s_1<⋯<s_n<T} (⊗_j G_{s_{j+1}-s_j})({w : (s_j, x - Σ_{l≥j} w_l)_j ∈ A}) ds`
  with `s_{n+1} = T` (the pushforward of `∏_j G_{s_{j+1}-s_j}(dw_j)` under
  `y_j = x - Σ_{l=j}^n w_l`, lines 4283-4285); for `n = 0` it is the unit mass on the empty
  tuple (lines 4287-4288).  Its total mass is `T^{2n}/(2n)!` (`chainMeasureRaw_univ`,
  `chainMeasure_univ`, `chainMeasure_univ_eq_chainMass`: the input `hmass` of
  `terminal_wick_paper` discharged), and it has no time atoms (`timeAtomless_chainMeasure`).
* Wrapper `terminal_wick_constructed_paper`: `L:terminal-wick` for `ν n = g_n^{T,x}`, with
  none of `hmass`, `hmeas`, `hK`; and `uniform_series_tail_terminal_wick_constructed_paper`:
  `L8Completed.uniform_series_tail_terminal_wick_paper` (which never took `hK`) with the
  chain measures `g_n^{T,x}`, its `hmass` and `hmeas` replaced by the cell continuity of each
  regularized covariance.
* Wrappers `terminal_wick_mono_constructed_paper` (the comparison sentence of
  `L:terminal-wick`, `TerminalWick.terminal_wick_mono_paper` with `ν n = g_n^{T,x}`, without
  `hmass`, `hmeas₁`, `hmeas₂`) and `uniform_series_tail_second_moment_constructed_paper` (the
  `B_1` sentence of `L:uniform-series-tail`,
  `UniformSeriesTail.uniform_series_tail_second_moment_paper` for the chain integrals over
  `g_n^{T,x}`, its `TerminalWickInput` discharged).

Supplied inputs: none.  Implicit hypotheses made explicit: `TimeAtomless ν` in the version for
abstract chain measures (proved for `g_n^{T,x}`); `0 ≤ T` in the definition of
`chainMeasure` (the time coordinate is mapped into `[0,T]` by `Set.projIcc`, which is the
identity on the support); `d ∈ {1,2,3}` for the identification and the mass.

Hypotheses carried but unused: `IsProbabilityMeasure P` (as in `terminal_wick_paper`).

Differences from the TeX:
* The time space of a point of `g_n^{T,x}` is `[0,T]` (as in `L:terminal-wick`, line 4292);
  the ordered simplex is the open one `0 < s_1 < ⋯ < s_n < T` (`OpenSimplex`), which is
  the TeX's open ordered simplex `[0,T]^n_<` (lines 550-551).
* In `d = 3`, `G` is `WaveGreen.waveGreen 3`, a documented definitional choice of `WaveGreen`
  (Mathlib's `Measure.toSphere` as surface measure).
* Not formalized: (ii) the `d = 3` Green-regularization paragraph (lines 4392-4398) and the
  symmetrization paragraph (lines 4384-4390), as in `TerminalWick`.
Lemmas marked "Auxiliary" serve only the Lean proof route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TerminalWick
public import StratonovichHAMSecondMoment.L8Completed

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace StratonovichHAMSecondMoment.TerminalWickInputs

open TerminalWick FiniteWick WaveGreen HomogHypothesis

/-! ### (i) Strong measurability of the chain product in `L²` -/

section Continuity
variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ}

/-- Auxiliary: the pairing sum over two points is the single covariance. -/
theorem wickSum_two (c : Fin 2 → Fin 2 → ℝ) : wickSum c Finset.univ = c 0 1 := by
  rw [wickSum_eq_sum_erase c Finset.univ 0 (Finset.mem_univ _) (fun x _ => Fin.zero_le x)]
  have h1 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  rw [h1, Finset.sum_singleton]
  have h2 : ({1} : Finset (Fin 2)).erase 1 = ∅ := by decide
  rw [h2, wickSum_empty, mul_one]

/-- The field value `W(p)` as an element of `L²(Ω)` (the one-point chain product). -/
def fieldL2 (hW : CenteredGaussianField W K P) (p : X) : Lp ℝ 2 P := prodL2 hW ![p]

/-- `E[W(p) W(q)] = K(p,q)`: the inner product of two field values in `L²`. -/
theorem inner_fieldL2 (hW : CenteredGaussianField W K P) (p q : X) :
    inner ℝ (fieldL2 hW p) (fieldL2 hW q) = K p q := by
  rw [fieldL2, fieldL2, inner_prodL2, wickSum_two]
  rfl

/-- `E|W(q) - W(p)|² = K(q,q) - 2K(p,q) + K(p,p)`. -/
theorem norm_sub_fieldL2_sq (hW : CenteredGaussianField W K P) (p q : X) :
    ‖fieldL2 hW q - fieldL2 hW p‖ ^ 2 = K q q - 2 * K p q + K p p := by
  rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_fieldL2, inner_fieldL2, inner_fieldL2, hW.symm q p]

/-- Mean-square continuity at `p` (the form of `TerminalWick.MeanSquareCellContinuous`) is
continuity of `p ↦ W(p)` into `L²` at `p`. -/
theorem continuousAt_fieldL2 [TopologicalSpace X] (hW : CenteredGaussianField W K P) {p : X}
    (h : Tendsto (fun q => K q q - 2 * K p q + K p p) (𝓝 p) (𝓝 0)) :
    ContinuousAt (fieldL2 hW) p := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have he : (fun q => ‖fieldL2 hW q - fieldL2 hW p‖) =
      fun q => Real.sqrt (K q q - 2 * K p q + K p p) := by
    funext q
    rw [← norm_sub_fieldL2_sq hW p q, Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  have hs := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at hs
  exact hs

/-- Auxiliary: the pairing sum of the Gram matrix of a tuple in a real inner product space. -/
def gramWick {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}
    (u : Fin k → E) : ℝ :=
  wickSum (fun a b => inner ℝ (u a) (u b)) Finset.univ

/-- Auxiliary: `gramWick` is continuous. -/
theorem continuous_gramWick {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} : Continuous (gramWick (E := E) (k := k)) := by
  unfold gramWick wickSum pairWeight
  exact continuous_finsetSum _ fun D _ => continuous_finsetProd _ fun x _ =>
    (continuous_apply x).inner (continuous_apply (D x))

/-- Auxiliary: concatenation of tuples is continuous. -/
theorem continuous_append {E : Type*} [TopologicalSpace E] {m n : ℕ} :
    Continuous fun uv : (Fin m → E) × (Fin n → E) => Fin.append uv.1 uv.2 := by
  refine continuous_pi fun a => ?_
  induction a using Fin.addCases with
  | left i => simp only [Fin.append_left]; exact (continuous_apply i).comp continuous_fst
  | right i => simp only [Fin.append_right]; exact (continuous_apply i).comp continuous_snd

/-- Auxiliary: concatenation commutes with applying a function pointwise. -/
theorem append_map {Y E : Type*} (f : Y → E) {m n : ℕ} (z : Fin m → Y) (z' : Fin n → Y)
    (a : Fin (m + n)) :
    Fin.append (fun i => f (z i)) (fun i => f (z' i)) a = f (Fin.append z z' a) := by
  induction a using Fin.addCases with
  | left i => simp only [Fin.append_left]
  | right i => simp only [Fin.append_right]

/-- `E[∏W(z) ∏W(z')]` as the pairing sum of the Gram matrix of the field values in `L²`. -/
theorem inner_prodL2_eq_gramWick (hW : CenteredGaussianField W K P) {m n : ℕ}
    (z : Fin m → X) (z' : Fin n → X) :
    inner ℝ (prodL2 hW z) (prodL2 hW z') =
      gramWick (Fin.append (fun i => fieldL2 hW (z i)) (fun i => fieldL2 hW (z' i))) := by
  rw [inner_prodL2, gramWick]
  congr 1
  funext a b
  rw [append_map, append_map, inner_fieldL2]

/-- `‖∏W(z) - ∏W(z₀)‖₂² = F(z,z) - 2F(z,z₀) + F(z₀,z₀)`, `F` the pairing sum of the Gram
matrix of the concatenated field values (TeX lines 4357-4359, by the Wick formula). -/
theorem norm_sub_prodL2_sq (hW : CenteredGaussianField W K P) {n : ℕ} (z z₀ : Fin n → X) :
    ‖prodL2 hW z - prodL2 hW z₀‖ ^ 2 =
      gramWick (Fin.append (fun i => fieldL2 hW (z i)) (fun i => fieldL2 hW (z i))) -
        2 * gramWick (Fin.append (fun i => fieldL2 hW (z i)) (fun i => fieldL2 hW (z₀ i))) +
        gramWick (Fin.append (fun i => fieldL2 hW (z₀ i)) (fun i => fieldL2 hW (z₀ i))) := by
  rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_prodL2_eq_gramWick, inner_prodL2_eq_gramWick, inner_prodL2_eq_gramWick]

/-- The chain product `z ↦ ∏_j W(z_j) ∈ L²` is continuous at every tuple of points at which
`p ↦ W(p) ∈ L²` is continuous (TeX lines 4357-4359). -/
theorem continuousAt_prodL2 [TopologicalSpace X] (hW : CenteredGaussianField W K P) {n : ℕ}
    {z₀ : Fin n → X} (hc : ∀ j, ContinuousAt (fieldL2 hW) (z₀ j)) :
    ContinuousAt (fun z => prodL2 hW z) z₀ := by
  set φ : (Fin n → X) → Fin n → Lp ℝ 2 P := fun z i => fieldL2 hW (z i) with hφ
  have hφc : ContinuousAt φ z₀ :=
    continuousAt_pi.2 fun i =>
      ContinuousAt.comp (f := fun z : Fin n → X => z i) (hc i) (continuous_apply i).continuousAt
  set G : (Fin n → X) → ℝ := fun z =>
    gramWick (Fin.append (φ z) (φ z)) - 2 * gramWick (Fin.append (φ z) (φ z₀)) +
      gramWick (Fin.append (φ z₀) (φ z₀)) with hG
  have hGc : ContinuousAt G z₀ := by
    have h1 : ContinuousAt (fun z => gramWick (Fin.append (φ z) (φ z))) z₀ :=
      continuous_gramWick.continuousAt.comp
        (continuous_append.continuousAt.comp (hφc.prodMk hφc))
    have h2 : ContinuousAt (fun z => gramWick (Fin.append (φ z) (φ z₀))) z₀ :=
      continuous_gramWick.continuousAt.comp
        (continuous_append.continuousAt.comp (hφc.prodMk continuousAt_const))
    exact (h1.sub (continuousAt_const.mul h2)).add continuousAt_const
  have hG0 : G z₀ = 0 := by simp only [hG]; ring
  have hlim : Tendsto G (𝓝 z₀) (𝓝 0) := hG0 ▸ hGc.tendsto
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have he : (fun z => ‖prodL2 hW z - prodL2 hW z₀‖) = fun z => Real.sqrt (G z) := by
    funext z
    rw [← Real.sqrt_sq (norm_nonneg (prodL2 hW z - prodL2 hW z₀)), norm_sub_prodL2_sq hW z z₀]
  rw [he]
  have hs := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at hs
  exact hs

end Continuity

section Measurability
open Finset

variable {d : ℕ} {T : ℝ}

/-- No time atoms: for every `n`, every vertex `j` and every time `t`, the chain measure of
`{z : time of z_j = t}` is zero.  True for `g_n^{T,x}` (`timeAtomless_chainMeasure`), whose
time marginal has a density (`E:terminal-chain-measure`, line 4278). -/
def TimeAtomless (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) : Prop :=
  ∀ n (j : Fin n) (t : ℝ), ν n {z | ((z j).1 : ℝ) = t} = 0

/-- Strong measurability of the chain product in `L²` (TeX lines 4357-4359): under the cell
continuity of `L:terminal-wick` (lines 4294-4296) and for chain measures without time atoms,
`z ↦ ∏_j W(z_j) ∈ L²` is a.e. strongly measurable.  It is continuous off the tuples with a time
in the finite set of cut points, and that set is null. -/
theorem aestronglyMeasurable_prodL2_of_cell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : Pt d T → Ω → ℝ} {K : Pt d T → Pt d T → ℝ} (hW : CenteredGaussianField W K P)
    (hcell : MeanSquareCellContinuous K) (ν : ∀ n : ℕ, Measure (Fin n → Pt d T))
    (hν : TimeAtomless ν) (n : ℕ) :
    AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n) := by
  obtain ⟨Z, hZ⟩ := hcell
  set U : Set (Fin n → Pt d T) := {z | ∀ j, ((z j).1 : ℝ) ∉ Z} with hUdef
  have htime : ∀ j : Fin n, Measurable fun z : Fin n → Pt d T => ((z j).1 : ℝ) :=
    fun j => measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply j))
  have hU : MeasurableSet U := by
    have : U = ⋂ j, (fun z : Fin n → Pt d T => ((z j).1 : ℝ)) ⁻¹' (↑Z : Set ℝ)ᶜ := by
      ext z; simp [hUdef]
    rw [this]
    exact MeasurableSet.iInter fun j => htime j Z.finite_toSet.measurableSet.compl
  have hcont : ContinuousOn (fun z : Fin n → Pt d T => prodL2 hW z) U := fun z hz =>
    (continuousAt_prodL2 hW fun j => continuousAt_fieldL2 hW (hZ (z j) (hz j))).continuousWithinAt
  have hnull : ν n Uᶜ = 0 := by
    have : Uᶜ = ⋃ j, ⋃ t ∈ (↑Z : Set ℝ), {z : Fin n → Pt d T | ((z j).1 : ℝ) = t} := by
      ext z; simp [hUdef]
    rw [this]
    refine measure_iUnion_null fun j => ?_
    exact (measure_biUnion_null_iff Z.finite_toSet.countable).2 fun t _ => hν n j t
  have hae : ∀ᵐ z ∂(ν n), z ∈ U := measure_eq_zero_iff_ae_notMem.1 hnull |>.mono
    fun z hz => by simpa using hz
  have h := hcont.aestronglyMeasurable (μ := ν n) hU
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h

/-- Auxiliary: for chain measures without time atoms, almost every tuple has all its times
outside a given finite set. -/
theorem ae_times_notMem (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) (hν : TimeAtomless ν)
    (Z : Finset ℝ) (n : ℕ) : ∀ᵐ z ∂(ν n), ∀ j, ((z j).1 : ℝ) ∉ Z := by
  have hnull : ν n {z : Fin n → Pt d T | ¬ ∀ j, ((z j).1 : ℝ) ∉ Z} = 0 := by
    have : {z : Fin n → Pt d T | ¬ ∀ j, ((z j).1 : ℝ) ∉ Z} =
        ⋃ j, ⋃ t ∈ (↑Z : Set ℝ), {z : Fin n → Pt d T | ((z j).1 : ℝ) = t} := by
      ext z; simp
    rw [this]
    refine measure_iUnion_null fun j => ?_
    exact (measure_biUnion_null_iff Z.finite_toSet.countable).2 fun t _ => hν n j t
  exact measure_eq_zero_iff_ae_notMem.1 hnull |>.mono fun z hz => by simpa using hz

/-- Auxiliary: a pairing weight of the Gram matrix of a tuple in a real inner product space. -/
def gramPairWeight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}
    (D : Fin k → Fin k) (u : Fin k → E) : ℝ :=
  pairWeight (fun a b => inner ℝ (u a) (u b)) Finset.univ D

/-- Auxiliary: `gramPairWeight` is continuous. -/
theorem continuous_gramPairWeight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (D : Fin k → Fin k) : Continuous (gramPairWeight (E := E) D) := by
  unfold gramPairWeight pairWeight
  exact continuous_finsetProd _ fun x _ => (continuous_apply x).inner (continuous_apply (D x))

/-- The pairing integrands `q ↦ ∏_{{a,b} ∈ D} K(τ_a, τ_b)` are a.e. strongly measurable for
`ν_m ⊗ ν_n` under the cell continuity of `L:terminal-wick` (lines 4294-4296), for chain
measures without time atoms.  No measurability of `K` is assumed: `K(p,q) = ⟪W(p), W(q)⟫` is
continuous at pairs of mean-square continuity points, and the tuples with a time at a cut
point are null. -/
theorem aestronglyMeasurable_pairWeight_of_cell {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : Pt d T → Ω → ℝ} {K : Pt d T → Pt d T → ℝ}
    (hW : CenteredGaussianField W K P) (hcell : MeanSquareCellContinuous K)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (hν : TimeAtomless ν) (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) :
    AEStronglyMeasurable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
      pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) Finset.univ D)
      ((ν m).prod (ν n)) := by
  obtain ⟨Z, hZ⟩ := hcell
  have heq : (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
      pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) Finset.univ D) =
      fun q => gramPairWeight D
        (Fin.append (fun i => fieldL2 hW (q.1 i)) (fun i => fieldL2 hW (q.2 i))) := by
    funext q
    unfold gramPairWeight
    congr 1
    funext a b
    rw [append_map, append_map, inner_fieldL2]
  rw [heq]
  set U : Set ((Fin m → Pt d T) × (Fin n → Pt d T)) :=
    {q | (∀ j, ((q.1 j).1 : ℝ) ∉ Z) ∧ ∀ j, ((q.2 j).1 : ℝ) ∉ Z} with hUdef
  have htime : ∀ {k : ℕ} (j : Fin k), Measurable fun z : Fin k → Pt d T => ((z j).1 : ℝ) :=
    fun j => measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply j))
  have hZm : MeasurableSet (↑Z : Set ℝ)ᶜ := Z.finite_toSet.measurableSet.compl
  have hU : MeasurableSet U := by
    have : U = (⋂ j, (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) => ((q.1 j).1 : ℝ)) ⁻¹'
        (↑Z : Set ℝ)ᶜ) ∩
        ⋂ j, (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) => ((q.2 j).1 : ℝ)) ⁻¹'
          (↑Z : Set ℝ)ᶜ := by
      ext q; simp [hUdef]
    rw [this]
    exact (MeasurableSet.iInter fun j => ((htime j).comp measurable_fst) hZm).inter
      (MeasurableSet.iInter fun j => ((htime j).comp measurable_snd) hZm)
  have hcont : ContinuousOn (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) => gramPairWeight D
      (Fin.append (fun i => fieldL2 hW (q.1 i)) (fun i => fieldL2 hW (q.2 i)))) U := by
    intro q hq
    have h1 : ContinuousAt (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
        fun i => fieldL2 hW (q.1 i)) q :=
      continuousAt_pi.2 fun i => ContinuousAt.comp
        (f := fun q : (Fin m → Pt d T) × (Fin n → Pt d T) => q.1 i)
        (continuousAt_fieldL2 hW (hZ _ (hq.1 i)))
        ((continuous_apply i).comp continuous_fst).continuousAt
    have h2 : ContinuousAt (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
        fun i => fieldL2 hW (q.2 i)) q :=
      continuousAt_pi.2 fun i => ContinuousAt.comp
        (f := fun q : (Fin m → Pt d T) × (Fin n → Pt d T) => q.2 i)
        (continuousAt_fieldL2 hW (hZ _ (hq.2 i)))
        ((continuous_apply i).comp continuous_snd).continuousAt
    exact ((continuous_gramPairWeight D).continuousAt.comp
      (continuous_append.continuousAt.comp (h1.prodMk h2))).continuousWithinAt
  have hae : ∀ᵐ q ∂((ν m).prod (ν n)), q ∈ U := by
    have ha := (Measure.quasiMeasurePreserving_fst (μ := ν m) (ν := ν n)).ae
      (ae_times_notMem ν hν Z m)
    have hb := (Measure.quasiMeasurePreserving_snd (μ := ν m) (ν := ν n)).ae
      (ae_times_notMem ν hν Z n)
    filter_upwards [ha, hb] with q hqa hqb
    exact ⟨hqa, hqb⟩
  have h := hcont.aestronglyMeasurable (μ := (ν m).prod (ν n)) hU
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h

/-- Each pairing integrand is integrable for `ν_m ⊗ ν_n` (bound `max(V,1)^{m+n}`), under the
cell continuity and for chain measures without time atoms; no measurability of `K`. -/
theorem integrable_pairWeight_of_cell {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : Pt d T → Ω → ℝ} {K : Pt d T → Pt d T → ℝ}
    (hW : CenteredGaussianField W K P) (hcell : MeanSquareCellContinuous K)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (hν : TimeAtomless ν) (V : ℝ) (hKV : ∀ x y, |K x y| ≤ V) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) :
    Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
      pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) Finset.univ D)
      ((ν m).prod (ν n)) := by
  refine Integrable.of_bound (aestronglyMeasurable_pairWeight_of_cell hW hcell ν hν m n D)
    (max V 1 ^ (m + n)) (ae_of_all _ fun q => ?_)
  unfold pairWeight
  rw [Real.norm_eq_abs, Finset.abs_prod]
  have h1 : ∏ x ∈ Finset.univ with x < D x,
      |K (Fin.append q.1 q.2 x) (Fin.append q.1 q.2 (D x))| ≤
      ∏ x ∈ Finset.univ with x < D x, (fun _ => max V 1) x :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun x _ => (hKV _ _).trans (le_max_left _ _)
  refine h1.trans ?_
  rw [Finset.prod_const]
  refine pow_le_pow_right₀ (le_max_right _ _) ?_
  exact (Finset.card_le_univ _).trans (by simp)

/-- `E:terminal-wick-formula` (TeX lines 4307-4328) without measurability of `K`: under the
cell continuity and for chain measures without time atoms,
`E[Y_m Y_n] = Σ_{D ∈ Π(m+n)} ∫ ∏_{{a,b} ∈ D} K(τ_a, τ_b) d(ν_m ⊗ ν_n)`. -/
theorem mixed_moment_eq_sum_pairings_of_cell {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : Pt d T → Ω → ℝ} {K : Pt d T → Pt d T → ℝ}
    (hW : CenteredGaussianField W K P) (hcell : MeanSquareCellContinuous K)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (hν : TimeAtomless ν) (V : ℝ) (hV0 : 0 ≤ V) (hV : ∀ x, K x x ≤ V) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
      ∑ D ∈ pairings (Finset.univ : Finset (Fin (m + n))), pairingIntegral ν K m n D := by
  rw [mixed_moment_eq_inner, inner_chainIntegral ν hW V hV0 hV
    (aestronglyMeasurable_prodL2_of_cell hW hcell ν hν)]
  unfold wickSum
  exact integral_finsetSum _ fun D _ =>
    integrable_pairWeight_of_cell hW hcell ν hν V (fun x y => hW.abs_le V hV x y) m n D

/-- `L:terminal-wick` (main TeX lines 4291-4336, proof 4338-4410 at edf7085f) for chain
measures without time atoms, with the strong measurability `hmeas` of
`TerminalWick.terminal_wick_paper` proved (`aestronglyMeasurable_prodL2_of_cell`) from the
lemma's cell continuity, and WITHOUT the measurability `hK` of `K` (an added hypothesis of
`terminal_wick_paper`, not implied by the TeX's assumptions): the pairing-by-pairing split
uses `integrable_pairWeight_of_cell` instead.  Conclusions exactly those of
`TerminalWick.terminal_wick_paper`. -/
theorem terminal_wick_paper_measurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ) (hW : CenteredGaussianField W K P)
    (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (hmass : ∀ n, ν n univ = chainMass d n T)
    (hν : TimeAtomless ν) :
    (∀ n, Integrable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n)) ∧
      ((chainIntegral ν hW 0 : Ω → ℝ) =ᵐ[P] fun _ => 1) ∧
      (∀ n, ‖chainIntegral ν hW n‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) *
        (⨆ p, K p p) ^ ((n : ℝ) / 2) * (T ^ (2 * n) / (2 * n).factorial)) ∧
      (∀ m n, ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
        ∑ D ∈ pairings (univ : Finset (Fin (m + n))), pairingIntegral ν K m n D) ∧
      (∀ m n (D : Fin (m + n) → Fin (m + n)),
        Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
          pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D)
          ((ν m).prod (ν n))) ∧
      (∀ m n, Odd (m + n) → ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P = 0) ∧
      ((∀ p q, 0 ≤ K p q) →
        (∀ m n (D : Fin (m + n) → Fin (m + n)), 0 ≤ pairingIntegral ν K m n D) ∧
        ∀ m n, 0 ≤ ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P) ∧
      (∀ r : ℝ, Summable fun n => ‖r ^ n • chainIntegral ν hW n‖) ∧
      ((∀ p q, 0 ≤ K p q) → ∀ r : ℝ,
        UniformSeriesTail.TerminalWickInput P (fun n => chainIntegral ν hW n) r) :=
by
  set V := ⨆ p, K p p with hVdef
  have hV : ∀ p, K p p ≤ V := fun p => le_ciSup hVfin p
  have hV0 : 0 ≤ V := supVar_nonneg hW hT.le hVfin
  have hmeas := aestronglyMeasurable_prodL2_of_cell hW hcell ν hν
  have hmassR : ∀ n, (ν n).real univ = T ^ (2 * n) / (2 * n).factorial := by
    intro n
    rw [measureReal_def, hmass n, chainMass_eq d hd n T hT.le, ENNReal.toReal_ofReal]
    positivity
  refine ⟨integrable_prodL2 ν hW V hV0 hV hmeas, ?_, fun n => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine chainIntegral_zero hW ν ?_
    rw [hmass 0, chainMass_eq d hd 0 T hT.le]; simp
  · have h := norm_chainIntegral_le ν hW V hV0 hV n
    rwa [hmassR n, sqrt_pow_eq_rpow V hV0] at h
  · exact fun m n => mixed_moment_eq_sum_pairings_of_cell hW hcell ν hν V hV0 hV m n
  · exact fun m n D =>
      integrable_pairWeight_of_cell hW hcell ν hν V (fun x y => hW.abs_le V hV x y) m n D
  · exact fun m n h => mixed_moment_odd ν hW V hV0 hV hmeas m n h
  · exact fun hpos => ⟨fun m n D => pairing_integral_nonneg ν hpos m n D,
      fun m n => mixed_moment_nonneg ν hW V hV0 hV hmeas hpos m n⟩
  · exact summable_norm_smul_chainIntegral ν hW V hV0 hV T hmassR
  · exact fun hpos r => terminalWickInput_of_nonneg ν hW V hV0 hV hmeas T hmassR hpos r

end Measurability

/-! ### (iii) The terminal-chain measures `g_n^{T,x}` -/

section ChainMeasure
open Finset

/-- The gaps `s_{j+1} - s_j` of a time tuple, with `s_{n+1} = T`
(`E:terminal-chain-measure`, lines 4276-4282). -/
def gap (T : ℝ) {n : ℕ} (s : Fin n → ℝ) (j : Fin n) : ℝ :=
  (Fin.snoc s T : Fin (n + 1) → ℝ) j.succ - s j

/-- The open ordered simplex `0 < s_1 < ⋯ < s_n < T` (the TeX's open ordered simplex
`[0,T]^n_<`, lines 550-551). -/
def OpenSimplex (T : ℝ) {n : ℕ} (s : Fin n → ℝ) : Prop :=
  (∀ j, 0 < s j) ∧ ∀ j, s j < (Fin.snoc s T : Fin (n + 1) → ℝ) j.succ

/-- Auxiliary: `s ↦ (s_1, …, s_n, T)_k` is continuous. -/
theorem continuous_snoc_apply (T : ℝ) {n : ℕ} (k : Fin (n + 1)) :
    Continuous fun s : Fin n → ℝ => (Fin.snoc s T : Fin (n + 1) → ℝ) k := by
  induction k using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact continuous_const
  | cast i => simp only [Fin.snoc_castSucc]; exact continuous_apply i

/-- Auxiliary: the gaps are continuous in the times. -/
theorem continuous_gap (T : ℝ) {n : ℕ} (j : Fin n) :
    Continuous fun s : Fin n → ℝ => gap T s j :=
  (continuous_snoc_apply T j.succ).sub (continuous_apply j)

/-- Auxiliary: the open simplex is measurable. -/
theorem measurableSet_openSimplex (T : ℝ) (n : ℕ) :
    MeasurableSet {s : Fin n → ℝ | OpenSimplex T s} := by
  have : {s : Fin n → ℝ | OpenSimplex T s} =
      (⋂ j, {s : Fin n → ℝ | 0 < s j}) ∩
        ⋂ j, {s : Fin n → ℝ | s j < (Fin.snoc s T : Fin (n + 1) → ℝ) j.succ} := by
    ext s; simp [OpenSimplex]
  rw [this]
  refine (MeasurableSet.iInter fun j => ?_).inter (MeasurableSet.iInter fun j => ?_)
  · exact measurableSet_lt measurable_const (measurable_pi_apply j)
  · exact measurableSet_lt (measurable_pi_apply j) (continuous_snoc_apply T j.succ).measurable

/-- Auxiliary: the gaps of `s : Fin (n+1) → ℝ` other than the last are those of its
initial segment with terminal time `s_{n+1}`. -/
theorem gap_castSucc (T : ℝ) {n : ℕ} (s : Fin (n + 1) → ℝ) (i : Fin n) :
    gap T s i.castSucc = gap (s (Fin.last n)) (Fin.init s) i := by
  unfold gap
  rw [Fin.snoc_init_self, Fin.succ_castSucc, Fin.snoc_castSucc]
  rfl

/-- Auxiliary: the last gap is `T - s_{n+1}`. -/
theorem gap_last (T : ℝ) {n : ℕ} (s : Fin (n + 1) → ℝ) :
    gap T s (Fin.last n) = T - s (Fin.last n) := by
  unfold gap
  rw [Fin.succ_last, Fin.snoc_last]

/-- Auxiliary: recursion of the open simplex at the last vertex. -/
theorem openSimplex_succ_iff (T : ℝ) {n : ℕ} (s : Fin (n + 1) → ℝ) :
    OpenSimplex T s ↔
      (0 < s (Fin.last n) ∧ s (Fin.last n) < T) ∧ OpenSimplex (s (Fin.last n)) (Fin.init s) := by
  have hsucc : ∀ i : Fin n, (Fin.snoc s T : Fin (n + 2) → ℝ) i.castSucc.succ =
      (Fin.snoc (Fin.init s) (s (Fin.last n)) : Fin (n + 1) → ℝ) i.succ := by
    intro i
    rw [Fin.snoc_init_self, Fin.succ_castSucc, Fin.snoc_castSucc]
  unfold OpenSimplex
  rw [Fin.forall_fin_succ', Fin.forall_fin_succ']
  simp only [Fin.succ_last, Fin.snoc_last, hsucc, Fin.init]
  tauto

open scoped Classical in
/-- The density of `g_n^{T,x}` in time (lines 4276-4282), integrated over space:
`chainWeightReal n T s = 1_{0<s_1<⋯<s_n<T} ∏_j (s_{j+1} - s_j)`, `s_{n+1} = T`. -/
theorem chainWeightReal_eq_ite : ∀ (n : ℕ) (T : ℝ) (s : Fin n → ℝ),
    chainWeightReal n T s = if OpenSimplex T s then ∏ j, ENNReal.ofReal (gap T s j) else 0 := by
  intro n
  induction n with
  | zero => intro T s; simp [chainWeightReal, OpenSimplex]
  | succ n ih =>
    intro T s
    rw [chainWeightReal, ih, Fin.prod_univ_castSucc, gap_last]
    simp only [gap_castSucc]
    by_cases h1 : 0 < s (Fin.last n) ∧ s (Fin.last n) < T
    · by_cases h2 : OpenSimplex (s (Fin.last n)) (Fin.init s)
      · rw [ite_eq_left h1, ite_eq_left h2,
          ite_eq_left ((openSimplex_succ_iff T s).2 ⟨h1, h2⟩), mul_comm]
      · rw [ite_eq_right h2, ite_eq_right fun h => h2 ((openSimplex_succ_iff T s).1 h).2, mul_zero]
    · rw [ite_eq_right h1, ite_eq_right fun h => h1 ((openSimplex_succ_iff T s).1 h).1, zero_mul]

/-- Auxiliary: on the open simplex every time is below `T`. -/
theorem lt_of_openSimplex : ∀ {n : ℕ} {T : ℝ} {s : Fin n → ℝ}, OpenSimplex T s →
    ∀ j, s j < T := by
  intro n
  induction n with
  | zero => intro T s _ j; exact j.elim0
  | succ n ih =>
    intro T s hs j
    obtain ⟨h1, h2⟩ := (openSimplex_succ_iff T s).1 hs
    induction j using Fin.lastCases with
    | last => exact h1.2
    | cast i => exact (ih h2 i).trans h1.2

/-- The time part of `g_n^{T,x}`: Lebesgue measure on `ℝ^n` with the density
`1_{0<s_1<⋯<s_n<T} ∏_j (s_{j+1} - s_j)` (the masses of the Green factors). -/
def timeMeasure (n : ℕ) (T : ℝ) : Measure (Fin n → ℝ) :=
  (volume : Measure (Fin n → ℝ)).withDensity (chainWeightReal n T)

/-- Auxiliary: measurability of `chainWeightReal n T`. -/
theorem measurable_chainWeightReal_right (n : ℕ) (T : ℝ) : Measurable (chainWeightReal n T) :=
  (measurable_chainWeightReal n).comp (measurable_const.prodMk measurable_id)

/-- The positions `y_j = x - Σ_{l ≥ j} w_l` of the chain read backwards from `x`, paired with
the times (`E:terminal-chain-measure`, lines 4283-4285). -/
def chainPoint {d n : ℕ} (x : Rd d) (s : Fin n → ℝ) (w : Fin n → Rd d) :
    Fin n → ℝ × Rd d :=
  fun j => (s j, x - ∑ l ∈ univ.filter (fun l => j ≤ l), w l)

/-- Auxiliary: `chainPoint` is jointly continuous. -/
theorem continuous_chainPoint {d n : ℕ} (x : Rd d) :
    Continuous fun q : (Fin n → ℝ) × (Fin n → Rd d) => chainPoint x q.1 q.2 := by
  refine continuous_pi fun j => ?_
  exact ((continuous_apply j).comp continuous_fst).prodMk
    (continuous_const.sub (continuous_finsetSum _ fun l _ =>
      (continuous_apply l).comp continuous_snd))

/-- Auxiliary: the map `(s, v) ↦ chainPoint x s ((s_{j+1} - s_j) v_j)_j`. -/
def chainMap {d n : ℕ} (T : ℝ) (x : Rd d) (q : (Fin n → ℝ) × (Fin n → Rd d)) :
    Fin n → ℝ × Rd d :=
  chainPoint x q.1 fun j => gap T q.1 j • q.2 j

/-- Auxiliary: `chainMap` is measurable. -/
theorem measurable_chainMap {d n : ℕ} (T : ℝ) (x : Rd d) :
    Measurable (chainMap (n := n) T x) := by
  have hscale : Continuous fun q : (Fin n → ℝ) × (Fin n → Rd d) =>
      fun j => gap T q.1 j • q.2 j :=
    continuous_pi fun j =>
      ((continuous_gap T j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd)
  exact ((continuous_chainPoint x).comp (continuous_fst.prodMk hscale)).measurable

/-- The terminal-chain measure `g_n^{T,x}` of `E:terminal-chain-measure` (main TeX lines
4275-4288), on `n`-tuples of points `(s_j, y_j)` of `ℝ × ℝ^d`: the image of
`timeMeasure n T ⊗ G_1^{⊗n}` under `(s, v) ↦ (s_j, x - Σ_{l ≥ j} (s_{l+1} - s_l) v_l)_j`.
By the scaling `G_h(hA) = h G_1(A)` this is the TeX's definition (`chainMeasureRaw_apply`). -/
def chainMeasureRaw (d n : ℕ) (T : ℝ) (x : Rd d) : Measure (Fin n → ℝ × Rd d) :=
  ((timeMeasure n T).prod (Measure.pi fun _ : Fin n => waveGreen d 1)).map (chainMap T x)

/-- Auxiliary: `⊗_j G_{h_j} = (∏_j h_j) · (v ↦ (h_j v_j)_j)_* G_1^{⊗n}` for `h_j > 0`
(scaling `WaveGreen.waveGreen_scaling`, lines 6131-6132). -/
theorem pi_waveGreen_eq (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) {n : ℕ} (h : Fin n → ℝ)
    (hh : ∀ j, 0 < h j) :
    Measure.pi (fun j => waveGreen d (h j)) =
      (∏ j, ENNReal.ofReal (h j)) •
        (Measure.pi fun _ : Fin n => waveGreen d 1).map (fun v j => h j • v j) := by
  have hmeas : Measurable fun v : Fin n → Rd d => fun j => h j • v j :=
    (continuous_pi fun j => (continuous_apply j).const_smul (h j)).measurable
  refine Measure.pi_eq fun S hS => ?_
  have hpre : (fun v : Fin n → Rd d => fun j => h j • v j) ⁻¹' univ.pi S =
      univ.pi fun j => (h j)⁻¹ • S j := by
    ext v
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    refine forall_congr' fun j => ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero (hh j).ne'), inv_inv]
  rw [Measure.smul_apply, Measure.map_apply hmeas (MeasurableSet.univ_pi hS), hpre,
    Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← waveGreen_scaling d hd (h j) (hh j) _
    ((hS j).const_smul_of_ne_zero (inv_ne_zero (hh j).ne')), smul_inv_smul₀ (hh j).ne']

/-- `E:terminal-chain-measure` (main TeX lines 4275-4285): for every measurable set `A` of
`n`-tuples of points,
`g_n^{T,x}(A) = ∫_{0<s_1<⋯<s_n<T} (⊗_j G_{s_{j+1}-s_j})({w : (s_j, x - Σ_{l≥j} w_l)_j ∈ A}) ds`,
`s_{n+1} = T`: Lebesgue measure on the ordered simplex times the pushforward of
`∏_j G_{s_{j+1}-s_j}(dw_j)` under `y_j = x - Σ_{l=j}^n w_l`. -/
theorem chainMeasureRaw_apply (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (n : ℕ) (T : ℝ) (x : Rd d)
    {A : Set (Fin n → ℝ × Rd d)} (hA : MeasurableSet A) :
    chainMeasureRaw d n T x A =
      ∫⁻ s in {s : Fin n → ℝ | OpenSimplex T s},
        Measure.pi (fun j => waveGreen d (gap T s j)) {w | chainPoint x s w ∈ A} := by
  have hpre := measurable_chainMap (n := n) T x hA
  rw [chainMeasureRaw, Measure.map_apply (measurable_chainMap T x) hA, Measure.prod_apply hpre,
    timeMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_chainWeightReal_right n T)
      (measurable_measure_prodMk_left hpre), ← lintegral_indicator (measurableSet_openSimplex T n)]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply, chainWeightReal_eq_ite]
  by_cases hs : OpenSimplex T s
  · have hgap : ∀ j, 0 < gap T s j := fun j => sub_pos.2 (hs.2 j)
    have hset : MeasurableSet {w : Fin n → Rd d | chainPoint x s w ∈ A} :=
      ((continuous_chainPoint x).comp (continuous_const.prodMk continuous_id)).measurable hA
    have hsc : Measurable fun v : Fin n → Rd d => fun j => gap T s j • v j :=
      (continuous_pi fun j => (continuous_apply j).const_smul (gap T s j)).measurable
    rw [ite_eq_left hs, indicator_of_mem (show s ∈ {s | OpenSimplex T s} from hs),
      pi_waveGreen_eq d hd _ hgap, Measure.smul_apply, Measure.map_apply hsc hset, smul_eq_mul]
    rfl
  · rw [ite_eq_right hs, indicator_of_notMem (show s ∉ {s | OpenSimplex T s} from hs), zero_mul]

/-- Auxiliary: the total mass of `chainMeasureRaw` before the Green masses are evaluated. -/
theorem chainMeasureRaw_univ_eq (d n : ℕ) (T : ℝ) (x : Rd d) :
    chainMeasureRaw d n T x univ = chainMassReal n T * ∏ _j : Fin n, waveGreen d 1 univ := by
  rw [chainMeasureRaw, Measure.map_apply (measurable_chainMap T x) MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod, timeMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Measure.pi_univ]
  rfl

/-- The mass of `g_n^{T,x}` is `T^{2n}/(2n)!` (TeX lines 4348-4351). -/
theorem chainMeasureRaw_univ (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (n : ℕ) (T : ℝ)
    (hT : 0 ≤ T) (x : Rd d) :
    chainMeasureRaw d n T x univ = ENNReal.ofReal (T ^ (2 * n) / (2 * n).factorial) := by
  rw [chainMeasureRaw_univ_eq, chainMassReal_eq n T hT, waveGreen_mass d hd 1 zero_le_one]
  simp

/-- Auxiliary: the time coordinates are moved into `[0,T]` (the identity on the support). -/
def toPt {d n : ℕ} {T : ℝ} (hT : 0 ≤ T) (z : Fin n → ℝ × Rd d) : Fin n → Pt d T :=
  fun j => (Set.projIcc 0 T hT (z j).1, (z j).2)

/-- Auxiliary: `toPt` is measurable. -/
theorem measurable_toPt {d n : ℕ} {T : ℝ} (hT : 0 ≤ T) : Measurable (toPt (d := d) (n := n) hT) :=
  by
  refine Continuous.measurable (continuous_pi fun j => ?_)
  exact (continuous_projIcc.comp ((continuous_apply j).fst)).prodMk (continuous_apply j).snd

/-- The terminal-chain measure `g_n^{T,x}` (`E:terminal-chain-measure`, lines 4275-4288) as a
measure on `n`-tuples of points of `[0,T] × ℝ^d`, the point set of `L:terminal-wick`. -/
def chainMeasure (d n : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d) : Measure (Fin n → Pt d T) :=
  (chainMeasureRaw d n T x).map (toPt hT)

/-- Auxiliary: `chainMeasure` has the mass of `chainMeasureRaw`. -/
theorem chainMeasure_univ_eq (d n : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d) :
    chainMeasure d n T hT x univ = chainMeasureRaw d n T x univ := by
  rw [chainMeasure, Measure.map_apply (measurable_toPt hT) MeasurableSet.univ, preimage_univ]

instance instIsFiniteMeasureChainMeasure (d n : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d) :
    IsFiniteMeasure (chainMeasure d n T hT x) := by
  constructor
  rw [chainMeasure_univ_eq, chainMeasureRaw_univ_eq, chainMassReal_eq n T hT]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.prod_lt_top fun _ _ => measure_lt_top _ _)

/-- The mass of `g_n^{T,x}` on `[0,T] × ℝ^d` is `T^{2n}/(2n)!`. -/
theorem chainMeasure_univ (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (x : Rd d) :
    chainMeasure d n T hT x univ = ENNReal.ofReal (T ^ (2 * n) / (2 * n).factorial) := by
  rw [chainMeasure_univ_eq, chainMeasureRaw_univ d hd n T hT]

/-- The input `hmass` of `TerminalWick.terminal_wick_paper`, discharged for `g_n^{T,x}`. -/
theorem chainMeasure_univ_eq_chainMass (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (n : ℕ) (T : ℝ)
    (hT : 0 ≤ T) (x : Rd d) :
    chainMeasure d n T hT x univ = chainMass d n T := by
  rw [chainMeasure_univ d hd n T hT, chainMass_eq d hd n T hT]

/-- `g_0^{T,x}` is the unit mass on the empty tuple (lines 4287-4288). -/
theorem chainMeasure_zero (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 ≤ T)
    (x : Rd d) : chainMeasure d 0 T hT x = Measure.dirac default := by
  have hmass := chainMeasure_univ d hd 0 T hT x
  simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    ENNReal.ofReal_one] at hmass
  ext S hS
  rcases Set.Subsingleton.eq_empty_or_singleton (Set.subsingleton_of_subsingleton (s := S))
    with h | ⟨a, h⟩
  · subst h; simp
  · rw [h, Measure.dirac_apply' _ (measurableSet_singleton a), Subsingleton.elim a default,
      Set.indicator_of_mem (mem_singleton _), Pi.one_apply,
      show ({default} : Set (Fin 0 → Pt d T)) = univ from Set.eq_univ_of_forall
        fun z => Subsingleton.elim z default, hmass]

/-- `g_n^{T,x}` has no time atoms (its time marginal has a density). -/
theorem timeAtomless_chainMeasure (d : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d) :
    TimeAtomless (fun n => chainMeasure d n T hT x) := by
  intro n j t
  have hS : MeasurableSet {s : Fin n → ℝ | ((Set.projIcc 0 T hT (s j) : ℝ)) = t} :=
    (measurableSet_singleton t).preimage
      (measurable_subtype_coe.comp (continuous_projIcc.measurable.comp (measurable_pi_apply j)))
  have hset : MeasurableSet {z : Fin n → Pt d T | ((z j).1 : ℝ) = t} :=
    (measurableSet_singleton t).preimage
      (measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply j)))
  have hpre : chainMap (n := n) T x ⁻¹' (toPt hT ⁻¹' {z : Fin n → Pt d T | ((z j).1 : ℝ) = t}) =
      {s : Fin n → ℝ | ((Set.projIcc 0 T hT (s j) : ℝ)) = t} ×ˢ univ := by
    ext q; simp [toPt, chainMap, chainPoint]
  have htime : timeMeasure n T {s : Fin n → ℝ | ((Set.projIcc 0 T hT (s j) : ℝ)) = t} = 0 := by
    rw [timeMeasure, withDensity_apply _ hS]
    have hnull : ∀ᵐ s ∂(volume : Measure (Fin n → ℝ)), s ∉ {s : Fin n → ℝ | s j = t} :=
      measure_eq_zero_iff_ae_notMem.1 (by
        rw [MeasureTheory.volume_pi]
        exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) j t)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hnull] with s hsS hsj
    rw [chainWeightReal_eq_ite]
    by_cases hs : OpenSimplex T s
    · exfalso
      refine hsj ?_
      have hmem : s j ∈ Icc 0 T := ⟨(hs.1 j).le, (lt_of_openSimplex hs j).le⟩
      simpa [Set.projIcc_of_mem hT hmem] using hsS
    · rw [ite_eq_right hs]
  dsimp only
  rw [chainMeasure, Measure.map_apply (measurable_toPt hT) hset, chainMeasureRaw,
    Measure.map_apply (measurable_chainMap T x) ((measurable_toPt hT) hset), hpre,
    Measure.prod_prod, htime, zero_mul]

/-- `L:terminal-wick` (main TeX lines 4291-4336, proof 4338-4410 at edf7085f) for the
terminal-chain measures `g_n^{T,x}` of `E:terminal-chain-measure` (lines 4275-4288),
constructed here (`chainMeasure`).  Hypotheses: `d ∈ {1,2,3}`, `T > 0`, a terminal point
`x ∈ ℝ^d`; a centered real Gaussian field on `[0,T] × ℝ^d` with covariance `K`;
`V = sup K(p,p) < ∞`; mean-square continuity on the open cells of a finite partition
(used: it gives the strong measurability and the measurability of the pairing integrands).
Neither the mass `hmass`, nor the strong measurability `hmeas`, nor the measurability `hK` of
`K` of `TerminalWick.terminal_wick_paper` remains a hypothesis; `hK` is not implied by the
TeX's assumptions and is replaced by `integrable_pairWeight_of_cell`.  Conclusions exactly those of
`TerminalWick.terminal_wick_paper` with `ν n = g_n^{T,x}`, `Y_n = Y_n(T,x)`. -/
theorem terminal_wick_constructed_paper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d) (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ)
    (hW : CenteredGaussianField W K P) (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K) :
    let ν : ∀ n : ℕ, Measure (Fin n → Pt d T) := fun n => chainMeasure d n T hT.le x
    (∀ n, Integrable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n)) ∧
      ((chainIntegral ν hW 0 : Ω → ℝ) =ᵐ[P] fun _ => 1) ∧
      (∀ n, ‖chainIntegral ν hW n‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) *
        (⨆ p, K p p) ^ ((n : ℝ) / 2) * (T ^ (2 * n) / (2 * n).factorial)) ∧
      (∀ m n, ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
        ∑ D ∈ pairings (univ : Finset (Fin (m + n))), pairingIntegral ν K m n D) ∧
      (∀ m n (D : Fin (m + n) → Fin (m + n)),
        Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
          pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D)
          ((ν m).prod (ν n))) ∧
      (∀ m n, Odd (m + n) → ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P = 0) ∧
      ((∀ p q, 0 ≤ K p q) →
        (∀ m n (D : Fin (m + n) → Fin (m + n)), 0 ≤ pairingIntegral ν K m n D) ∧
        ∀ m n, 0 ≤ ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P) ∧
      (∀ r : ℝ, Summable fun n => ‖r ^ n • chainIntegral ν hW n‖) ∧
      ((∀ p q, 0 ≤ K p q) → ∀ r : ℝ,
        UniformSeriesTail.TerminalWickInput P (fun n => chainIntegral ν hW n) r) :=
  terminal_wick_paper_measurable P d hd T hT W K hW hVfin hcell
    (fun n => chainMeasure d n T hT.le x)
    (fun n => chainMeasure_univ_eq_chainMass d hd n T hT.le x)
    (timeAtomless_chainMeasure d T hT.le x)

/-- `L:uniform-series-tail` (main TeX lines 4419-4464) with its `L:terminal-wick` input
discharged, for the constructed terminal-chain measures `g_n^{T,x}`: this is
`L8Completed.uniform_series_tail_terminal_wick_paper` with `ν ε δ n = g_n^{T,x}` (the TeX's
fixed chain measures), in which the mass `hmass` and the strong measurability `hmeas` are
discharged; in their place it takes the cell continuity of `L:terminal-wick` for each
regularized covariance `K ε δ`, `ε, δ > 0`.  All other hypotheses and all conclusions are
those of `uniform_series_tail_terminal_wick_paper`. -/
theorem uniform_series_tail_terminal_wick_constructed_paper {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (T : ℝ) (hT : 0 < T) (x : Rd d) (W : ℝ → ℝ → Pt d T → Ω → ℝ)
    (K : ℝ → ℝ → Pt d T → Pt d T → ℝ)
    (hW : ∀ ε δ, CenteredGaussianField (W ε δ) (K ε δ) P)
    (hVfin : ∀ ε δ : ℝ, 0 < ε → 0 < δ → BddAbove (Set.range fun p => K ε δ p p))
    (hcell : ∀ ε δ : ℝ, 0 < ε → 0 < δ → MeanSquareCellContinuous (K ε δ))
    (hKpos : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ p q, 0 ≤ K ε δ p q)
    (X : ℕ → Lp ℝ 2 P) (r B : ℝ) (hr : 1 < r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n :
        Lp ℝ 2 P) ω) ^ 2 ∂P ≤ B)
    (hX : ∀ n, Tendsto
      (fun p : ℝ × ℝ => chainIntegral (fun n => chainMeasure d n T hT.le x) (hW p.1 p.2) n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n))) :
    (Summable fun n => ‖X n‖) ∧
      Tendsto (fun p : ℝ × ℝ =>
          ∑' n, chainIntegral (fun n => chainMeasure d n T hT.le x) (hW p.1 p.2) n)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (∑' n, X n)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n,
        ‖chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n‖ ≤
          Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ n, ‖X n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ N : ℕ,
        ‖∑' n, chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) (n + (N + 1))‖ ≤
          Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ N : ℕ, ‖∑' n, X (n + (N + 1))‖ ≤ Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ →
        Summable fun n => ‖chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n‖) :=
  L8Completed.uniform_series_tail_terminal_wick_paper P hd T hT W K hW hVfin
    (fun _ _ => fun n => chainMeasure d n T hT.le x)
    (fun _ _ _ _ n => chainMeasure_univ_eq_chainMass d hd n T hT.le x)
    (fun ε δ hε hδ n => aestronglyMeasurable_prodL2_of_cell (hW ε δ) (hcell ε δ hε hδ)
      (fun n => chainMeasure d n T hT.le x) (timeAtomless_chainMeasure d T hT.le x) n)
    hKpos X r B hr hB hX

/-- The comparison sentence of `L:terminal-wick` (main TeX lines 4331-4333, proof 4404-4406 at
edf7085f) for the constructed terminal-chain measures `g_n^{T,x}` of
`E:terminal-chain-measure` (lines 4275-4288): this is `TerminalWick.terminal_wick_mono_paper`
with `ν n = g_n^{T,x}`, its mass input `hmass` discharged by `chainMeasure_univ_eq_chainMass`
and its strong measurability inputs `hmeas₁`, `hmeas₂` discharged by
`aestronglyMeasurable_prodL2_of_cell` (from each field's cell continuity and
`timeAtomless_chainMeasure`).  Hypotheses, all the TeX's: `d ∈ {1,2,3}`, `T > 0`, a terminal
point `x ∈ ℝ^d`; two centered real Gaussian fields on `[0,T] × ℝ^d` with covariances `K₁`,
`K₂` (lines 4292-4293), each with `sup K_i(p,p) < ∞` (line 4294) and mean-square continuity on
the open cells of a finite partition (lines 4294-4296); the entrywise comparison
`0 ≤ K₁ ≤ K₂` (line 4332).  No hypothesis is added.  Conclusion:
`E[Y¹_m Y¹_n] ≤ E[Y²_m Y²_n]` for all `m, n` (line 4333, "all finite partial-order second
moments", including `m ≠ n`).  `IsProbabilityMeasure` (the TeX's setting) is carried, unused. -/
theorem terminal_wick_mono_constructed_paper {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₁fin : BddAbove (Set.range fun p => K₁ p p))
    (hV₂fin : BddAbove (Set.range fun p => K₂ p p))
    (hcell₁ : MeanSquareCellContinuous K₁) (hcell₂ : MeanSquareCellContinuous K₂)
    (h0 : ∀ p q, 0 ≤ K₁ p q) (h12 : ∀ p q, K₁ p q ≤ K₂ p q) (m n : ℕ) :
    ∫ ω, chainIntegral (fun n => chainMeasure d n T hT.le x) hW₁ m ω *
        chainIntegral (fun n => chainMeasure d n T hT.le x) hW₁ n ω ∂P₁ ≤
      ∫ ω, chainIntegral (fun n => chainMeasure d n T hT.le x) hW₂ m ω *
        chainIntegral (fun n => chainMeasure d n T hT.le x) hW₂ n ω ∂P₂ :=
  terminal_wick_mono_paper P₁ P₂ d hd T hT W₁ K₁ hW₁ W₂ K₂ hW₂ hV₁fin hV₂fin hcell₁ hcell₂
    (fun n => chainMeasure d n T hT.le x)
    (fun n => chainMeasure_univ_eq_chainMass d hd n T hT.le x)
    (aestronglyMeasurable_prodL2_of_cell hW₁ hcell₁ (fun n => chainMeasure d n T hT.le x)
      (timeAtomless_chainMeasure d T hT.le x))
    (aestronglyMeasurable_prodL2_of_cell hW₂ hcell₂ (fun n => chainMeasure d n T hT.le x)
      (timeAtomless_chainMeasure d T hT.le x))
    h0 h12 m n

/-- The last sentence of `L:uniform-series-tail` (main TeX lines 4441-4442, proof line 4462 at
edf7085f) for chain integrals over the constructed terminal-chain measures `g_n^{T,x}`: this is
`UniformSeriesTail.uniform_series_tail_second_moment_paper` with
`Y^{ε,δ}_n = ∫ ∏_j W^{ε,δ}(z_j) g_n^{T,x}(dz)`, its supplied `L:terminal-wick` input
`TerminalWickInput` discharged by `terminal_wick_constructed_paper` (last conclusion: absolute
`L²` convergence at `r` and nonnegative mixed moments, from the cell continuity and the
nonnegative covariance).  Hypotheses, the TeX's (lines 4419-4442): `d ∈ {1,2,3}`, `T > 0`,
`x ∈ ℝ^d` (the fixed `(T,x)`, line 4420); for every `ε, δ > 0` the field `W ε δ` satisfies
the hypotheses of `L:terminal-wick` (centered Gaussian with covariance `K ε δ`, bounded
variance, cell continuity) and has nonnegative covariance (lines 4421-4422); `r > 1` and
`sup_{ε,δ>0} E|u^{ε,δ}(r)|² ≤ B` (`B = B_r`); `Y^{ε,δ}_n → X_n` in `L²` as `ε, δ ↓ 0`, for
each `n`; and `E|u^{ε,δ}(1)|² ≤ B₁` for all `ε, δ > 0` (line 4441).  Conclusion:
`E|u|² ≤ B₁` for `u = Σ X_n` (lines 4441-4442).  Formalization artifact, as in
`uniform_series_tail_terminal_wick_constructed_paper`: the Gaussian-field structure `hW ε δ` is
assumed for every real pair `(ε, δ)` (it indexes the chain integrals of the family); only its
values at positive pairs enter the hypotheses and the conclusion.  No other hypothesis is
added.  `IsProbabilityMeasure P` is the TeX's setting. -/
theorem uniform_series_tail_second_moment_constructed_paper {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (T : ℝ) (hT : 0 < T) (x : Rd d) (W : ℝ → ℝ → Pt d T → Ω → ℝ)
    (K : ℝ → ℝ → Pt d T → Pt d T → ℝ)
    (hW : ∀ ε δ, CenteredGaussianField (W ε δ) (K ε δ) P)
    (hVfin : ∀ ε δ : ℝ, 0 < ε → 0 < δ → BddAbove (Set.range fun p => K ε δ p p))
    (hcell : ∀ ε δ : ℝ, 0 < ε → 0 < δ → MeanSquareCellContinuous (K ε δ))
    (hKpos : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ p q, 0 ≤ K ε δ p q)
    (X : ℕ → Lp ℝ 2 P) (r B B₁ : ℝ) (hr : 1 < r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n :
        Lp ℝ 2 P) ω) ^ 2 ∂P ≤ B)
    (hX : ∀ n, Tendsto
      (fun p : ℝ × ℝ => chainIntegral (fun n => chainMeasure d n T hT.le x) (hW p.1 p.2) n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n)))
    (hB₁ : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n :
        Lp ℝ 2 P) ω) ^ 2 ∂P ≤ B₁) :
    ∫ ω, ((∑' n, X n : Lp ℝ 2 P) ω) ^ 2 ∂P ≤ B₁ :=
  UniformSeriesTail.uniform_series_tail_second_moment_paper
    (fun ε δ n => chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n) X r B B₁ hr
    (fun ε δ hε hδ =>
      (terminal_wick_constructed_paper P d hd T hT x (W ε δ) (K ε δ) (hW ε δ)
        (hVfin ε δ hε hδ) (hcell ε δ hε hδ)).2.2.2.2.2.2.2.2 (hKpos ε δ hε hδ) r)
    hB hX hB₁

end ChainMeasure

end StratonovichHAMSecondMoment.TerminalWickInputs
