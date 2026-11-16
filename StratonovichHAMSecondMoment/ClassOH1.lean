module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L14, item O (part 1): the real Sobolev space `H¹(ℝ^d;ℝ)` as a topological space, and the
topological joint continuity of the four-linear pairing of Proposition `P:spatial-four-linear`
(`notes/integrated_spatial_occupation.tex`, statement lines 297-315, proof lines 317-398, at
revision 39f2597a; the continuity sentence is lines 307-308, its proof lines 374-376).

The space.  `H1R d` is the graph `{(f, ∇f)}` of the weak gradient inside
`L²(ℝ^d;ℝ) × L²(ℝ^d;ℝ^d)` (Mathlib's `Lp` classes), with the subspace topology of the product.
This is the TeX's own description of `H¹` in the proof of `P:spatial-four-linear` (lines
356-358: "its closed isometric image `f ↦ (f, ∇f)` in `L²(ℝ^d)^{d+1}`").  Its topology is that of
Mathlib's Bessel-potential space `H^{1}(ℝ^d)` (wave L13 item K5a, `H1Mathlib`): the map
`toMH1 : H1R d → H^{1}(ℝ^d)`, `(f, g) ↦ H1Mathlib.toH1`, satisfies
`‖toMH1 p - toMH1 q‖² = ‖f_p - f_q‖₂² + (2π)⁻² ‖g_p - g_q‖₂²` (`norm_toMH1_sub_sq`), is
Lipschitz and antiLipschitz (`lipschitz_toMH1`, `antilipschitz_toMH1`), hence a topological
embedding (`isEmbedding_toMH1`), and the topology of `H1R d` is the one induced from `H^{1}`
(`topology_eq_induced`).  Every real `H¹` pair `(f, g)` (`SpatialFourLinear.IsH1Pair`) has a class
`ofPair` in `H1R d` with a.e.-equal representatives.

Formalized:
* `continuous_C4`: under `SquareBound Γ α R` (`R ≥ 0`, `0 < α < 4`, `Γ` locally finite) the map
  `(f₁,f₂,f₃,f₄) ↦ C₄(f₁,f₂,f₃,f₄)` is continuous on `(H1R d)⁴` (product topology);
  `continuous_sqPair_toReal`: the real square pairings `(f,h) ↦ B_Γ(f²,h²)` are continuous on
  `H1R d × H1R d` (TeX lines 375-376, "`A_sp` and the square pairings are continuous");
* `continuous_Q`: the map `Q : H¹ → H_sp` of `L:occupation-raw-square` (wave L14 item K1a,
  `OccupationCompletion.Q`; `notes/integrated_occupation_ceiling.tex` lines 24-43) is continuous
  on `H1R d` (K1a proved only the sequential form);
* `spatial_four_linear_whole_paper`: `P:spatial-four-linear` under the section's standing
  assumptions (lines 4-10: `H:homog` with `a = α₀`, `Γ ≠ 0`) with every conclusion: the
  conclusions of `SpatialOccupationL7Completed.spatial_four_linear_paper_completed` together with
  the topological joint continuity of `C₄` on `(H¹)⁴` (`H¹ = H1R d`, whose topology is Mathlib's
  `H^{1}` topology by `isEmbedding_toMH1`, also stated in the wrapper).  The sequential form
  of the earlier modules is kept as a conjunct.
* `occupation_raw_square_continuous_paper`: topological continuity of `Q` on `H1R d` under the
  standing assumptions of `L:occupation-raw-square` (`H:homog`, `Γ ≠ 0`).

Supplied inputs: none.  `SquareBound Γ α R_0` is `SpatialFourLinear.squareBound_R0` with the
density statement `H1Density.h1TestDense` (wave L7-c).

Implicit hypotheses made explicit: none beyond those of the wrapped results; the topology on
`(H¹)⁴` is the product topology.  Differences from the TeX: continuity is deduced from the
sequential continuity of `SpatialFourLinear.C4_tendsto` (telescoping, as in the TeX) because
`H1R d` is a metric space; the TeX's `N(f) ≤ ‖f‖_{H¹}` step is replaced by the continuity of `N`
along `H¹` convergence.  Lemmas marked "Auxiliary to the Lean proof route" have no manuscript
label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.H1Mathlib
public import StratonovichHAMSecondMoment.SpatialOccupationL7Completed
public import StratonovichHAMSecondMoment.OccupationCompletion

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Topology
open scoped ENNReal BesselPotentialSpace

namespace StratonovichHAMSecondMoment.ClassOH1

open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (HasWeakGradient MemH1)
open SpatialFourLinear (IsH1Pair H1Tendsto C4 SquareBound Nnorm)
open SpatialStaticControls (zE)
open OccupationKernelRow (pairing pairMeasure)

variable {d : ℕ}

/-! ### The space `H¹(ℝ^d;ℝ)` as the graph of the weak gradient -/

/-- `L²(ℝ^d;ℝ)` (Lebesgue classes). -/
abbrev L2R (d : ℕ) := Lp ℝ 2 (volume : Measure (Rd d))

/-- `L²(ℝ^d;ℝ^d)` (Lebesgue classes of vector fields). -/
abbrev L2V (d : ℕ) := Lp (Rd d) 2 (volume : Measure (Rd d))

/-- The graph `{(f, ∇f)}` of the weak gradient in `L²(ℝ^d;ℝ) × L²(ℝ^d;ℝ^d)` (TeX lines
356-358 of `integrated_spatial_occupation.tex`): pairs of classes whose representatives satisfy
`WeakSobolev.HasWeakGradient`. -/
def graph (d : ℕ) : Set (L2R d × L2V d) :=
  {p | HasWeakGradient (p.1 : Rd d → ℝ) (p.2 : Rd d → Rd d)}

/-- The real Sobolev space `H¹(ℝ^d;ℝ)` (`notes_stratonovich_ham_second_moment.tex` lines
748-750), as the subtype `graph d` with the topology of `L² × L²`. -/
abbrev H1R (d : ℕ) := ↥(graph d)

/-- The function part of `p ∈ H¹` (a representative of its `L²` class). -/
abbrev fn (p : H1R d) : Rd d → ℝ := ((p : L2R d × L2V d).1 : Rd d → ℝ)

/-- The gradient part of `p ∈ H¹` (a representative of its `L²` class). -/
abbrev grd (p : H1R d) : Rd d → Rd d := ((p : L2R d × L2V d).2 : Rd d → Rd d)

/-- Every element of `H1R d` is an `H¹` pair. -/
theorem isH1Pair (p : H1R d) : IsH1Pair (fn p) (grd p) := ⟨Lp.memLp _, Lp.memLp _, p.2⟩

/-- Every element of `H1R d` lies in `WeakSobolev.MemH1`. -/
theorem memH1 (p : H1R d) : MemH1 (fn p) := ⟨Lp.memLp _, grd p, Lp.memLp _, p.2⟩

/-- Auxiliary to the Lean proof route: weak gradients are stable under a.e. changes of the
function and of the gradient. -/
theorem hasWeakGradient_congr_ae {f f' : Rd d → ℝ} {g g' : Rd d → Rd d}
    (hw : HasWeakGradient f g) (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    HasWeakGradient f' g' := by
  intro φ hφ v
  have e1 : ∫ x, f' x * fderiv ℝ φ x v = ∫ x, f x * fderiv ℝ φ x v :=
    integral_congr_ae (hf.mono fun x hx => by simp only; rw [hx])
  have e2 : ∫ x, inner ℝ (g' x) v * φ x = ∫ x, inner ℝ (g x) v * φ x :=
    integral_congr_ae (hg.mono fun x hx => by simp only; rw [hx])
  rw [e1, e2]
  exact hw φ hφ v

/-- The class in `H1R d` of an `H¹` pair `(f, g)`. -/
def ofPair {f : Rd d → ℝ} {g : Rd d → Rd d} (h : IsH1Pair f g) : H1R d :=
  ⟨(h.1.toLp f, h.2.1.toLp g),
    hasWeakGradient_congr_ae h.2.2 h.1.coeFn_toLp.symm h.2.1.coeFn_toLp.symm⟩

/-- The function part of `ofPair h` is `f` a.e. -/
theorem fn_ofPair {f : Rd d → ℝ} {g : Rd d → Rd d} (h : IsH1Pair f g) :
    fn (ofPair h) =ᵐ[volume] f :=
  h.1.coeFn_toLp

/-- The gradient part of `ofPair h` is `g` a.e. -/
theorem grd_ofPair {f : Rd d → ℝ} {g : Rd d → Rd d} (h : IsH1Pair f g) :
    grd (ofPair h) =ᵐ[volume] g :=
  h.2.1.coeFn_toLp

/-! ### The embedding into Mathlib's `H^{1}` -/

/-- The element of Mathlib's `H^{1}(ℝ^d)` (wave L13 item K5a, `H1Mathlib.toH1`) defined by
`p ∈ H¹`. -/
def toMH1 (p : H1R d) : H^{1}(Rd d) := H1Mathlib.toH1 (memH1 p)

/-- Auxiliary to the Lean proof route: the norm identity of `H1Mathlib.norm_toH1_sq` for a
difference, `‖toH1 f₁ - toH1 f₂‖² = ∫ (f₁-f₂)² + (2π)⁻² ∫ ‖g₁-g₂‖²`. -/
theorem norm_toH1_sub_sq {f₁ f₂ : Rd d → ℝ} (h₁ : MemH1 f₁) (h₂ : MemH1 f₂)
    {g₁ g₂ : Rd d → Rd d} (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume)
    (hw₁ : HasWeakGradient f₁ g₁) (hw₂ : HasWeakGradient f₂ g₂) :
    ‖H1Mathlib.toH1 h₁ - H1Mathlib.toH1 h₂‖ ^ 2 =
      (∫ x, (f₁ x - f₂ x) ^ 2) + ((2 * π) ^ 2)⁻¹ * ∫ x, ‖g₁ x - g₂ x‖ ^ 2 := by
  have hL := h₁.1.sub h₂.1
  have hG := hg₁.sub hg₂
  have hW := H1Mathlib.hasWeakGradient_sub h₁.1 h₂.1 hg₁ hg₂ hw₁ hw₂
  rw [← BesselPotentialSpace.norm_toLp_eq, BesselPotentialSpace.toLp_sub,
    H1Mathlib.norm_sq_of_besselPotential_eq hL hG hW]
  · rfl
  · rw [H1Mathlib.toDistr_sub h₁.1 h₂.1, map_sub, ← H1Mathlib.toH1_toDistr h₁,
      ← H1Mathlib.toH1_toDistr h₂, BesselPotentialSpace.bessel_toDistr_eq_toLp,
      BesselPotentialSpace.bessel_toDistr_eq_toLp, ← Lp.toTemperedDistributionCLM_apply,
      ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_sub]

/-- Auxiliary to the Lean proof route: `∫ ‖u - v‖² = ‖u - v‖²_{L²}` on representatives. -/
theorem integral_norm_sub_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : Lp E 2 (volume : Measure (Rd d))) :
    ∫ x, ‖(u : Rd d → E) x - v x‖ ^ 2 = ‖u - v‖ ^ 2 := by
  have hm : MemLp (fun x => (u : Rd d → E) x - v x) 2 volume := (Lp.memLp u).sub (Lp.memLp v)
  rw [H1Mathlib.integral_norm_sq_eq hm, Lp.norm_def]
  congr 2
  exact eLpNorm_congr_ae (Lp.coeFn_sub u v).symm

/-- **Norm identity on `H1R d`**: `‖toMH1 p - toMH1 q‖² = ‖f_p - f_q‖₂² + (2π)⁻² ‖g_p - g_q‖₂²`
(Mathlib's `2π` convention, as in `H1Mathlib.norm_toH1_sq`). -/
theorem norm_toMH1_sub_sq (p q : H1R d) :
    ‖toMH1 p - toMH1 q‖ ^ 2 = ‖(p : L2R d × L2V d).1 - (q : L2R d × L2V d).1‖ ^ 2 +
      ((2 * π) ^ 2)⁻¹ * ‖(p : L2R d × L2V d).2 - (q : L2R d × L2V d).2‖ ^ 2 := by
  rw [toMH1, toMH1, norm_toH1_sub_sq (memH1 p) (memH1 q) (Lp.memLp _) (Lp.memLp _) p.2 q.2,
    ← integral_norm_sub_sq, ← integral_norm_sub_sq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Auxiliary to the Lean proof route: the distance of `H1R d` is the maximum of the two `L²`
distances. -/
theorem dist_eq (p q : H1R d) :
    dist p q = max ‖(p : L2R d × L2V d).1 - (q : L2R d × L2V d).1‖
      ‖(p : L2R d × L2V d).2 - (q : L2R d × L2V d).2‖ := by
  rw [Subtype.dist_eq, Prod.dist_eq, dist_eq_norm, dist_eq_norm]

/-- `toMH1` is `2`-Lipschitz. -/
theorem lipschitz_toMH1 : LipschitzWith 2 (toMH1 (d := d)) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [dist_eq_norm, dist_eq p q]
  have h := norm_toMH1_sub_sq p q
  set a := ‖(p : L2R d × L2V d).1 - (q : L2R d × L2V d).1‖
  set b := ‖(p : L2R d × L2V d).2 - (q : L2R d × L2V d).2‖
  set D := ‖toMH1 p - toMH1 q‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hD : 0 ≤ D := norm_nonneg _
  have hc0 : 0 ≤ ((2 * π) ^ 2)⁻¹ := by positivity
  have hc1 : ((2 * π) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  have hma := le_max_left a b
  have hmb := le_max_right a b
  have hcb : ((2 * π) ^ 2)⁻¹ * b ^ 2 ≤ b ^ 2 := by nlinarith [sq_nonneg b]
  have hsq : D ^ 2 ≤ (2 * max a b) ^ 2 := by nlinarith
  push_cast
  exact (pow_le_pow_iff_left₀ hD (by linarith [ha.trans hma]) two_ne_zero).1 hsq

/-- `toMH1` is `7`-antiLipschitz (`2π < 7`). -/
theorem antilipschitz_toMH1 : AntilipschitzWith 7 (toMH1 (d := d)) := by
  refine AntilipschitzWith.of_le_mul_dist fun p q => ?_
  rw [dist_eq_norm (toMH1 p), dist_eq p q]
  have h := norm_toMH1_sub_sq p q
  set a := ‖(p : L2R d × L2V d).1 - (q : L2R d × L2V d).1‖
  set b := ‖(p : L2R d × L2V d).2 - (q : L2R d × L2V d).2‖
  set D := ‖toMH1 p - toMH1 q‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hD : 0 ≤ D := norm_nonneg _
  have hpi : 0 < (2 * π) ^ 2 := by positivity
  have hpi7 : (2 * π) ^ 2 < 49 := by nlinarith [Real.pi_lt_d2, Real.pi_gt_three]
  have hc : ((2 * π) ^ 2)⁻¹ * (2 * π) ^ 2 = 1 := inv_mul_cancel₀ hpi.ne'
  have hA : a ^ 2 ≤ D ^ 2 := by nlinarith [mul_nonneg (inv_nonneg.2 hpi.le) (sq_nonneg b)]
  have hB : b ^ 2 ≤ 49 * D ^ 2 := by
    have : ((2 * π) ^ 2)⁻¹ * b ^ 2 ≤ D ^ 2 := by nlinarith [sq_nonneg a]
    have h2 : b ^ 2 ≤ (2 * π) ^ 2 * D ^ 2 := by
      have := mul_le_mul_of_nonneg_left this hpi.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at this
    nlinarith [sq_nonneg D]
  have hA' : a ≤ 7 * D := by nlinarith [sq_nonneg (a - 7 * D)]
  have hB' : b ≤ 7 * D := by nlinarith [sq_nonneg (b - 7 * D)]
  push_cast
  exact max_le hA' hB'

/-- **`H1R d` carries the topology of Mathlib's `H^{1}(ℝ^d)`**: `toMH1` is a topological
(indeed uniform) embedding. -/
theorem isEmbedding_toMH1 : IsEmbedding (toMH1 (d := d)) :=
  (antilipschitz_toMH1.isUniformEmbedding lipschitz_toMH1.uniformContinuous).isEmbedding

/-- The topology of `H1R d` is the topology induced by `toMH1` from Mathlib's `H^{1}(ℝ^d)`. -/
theorem topology_eq_induced :
    (inferInstance : TopologicalSpace (H1R d)) =
      TopologicalSpace.induced (toMH1 (d := d)) inferInstance :=
  isEmbedding_toMH1.isInducing.eq_induced

/-! ### Topological continuity -/

/-- Auxiliary to the Lean proof route: convergence in `H1R d` is `H¹` convergence of
representatives (`SpatialFourLinear.H1Tendsto`). -/
theorem h1Tendsto_of_tendsto {u : ℕ → H1R d} {p : H1R d} (h : Tendsto u atTop (𝓝 p)) :
    H1Tendsto (fun n => fn (u n)) (fun n => grd (u n)) (fn p) (grd p) := by
  have h1 : Tendsto (fun n => (u n : L2R d × L2V d).1) atTop (𝓝 (p : L2R d × L2V d).1) :=
    ((continuous_fst.comp continuous_subtype_val).tendsto p).comp h
  have h2 : Tendsto (fun n => (u n : L2R d × L2V d).2) atTop (𝓝 (p : L2R d × L2V d).2) :=
    ((continuous_snd.comp continuous_subtype_val).tendsto p).comp h
  exact ⟨(Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h1,
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h2⟩

/-- **Joint continuity of `C₄` on `(H¹)⁴`** (TeX lines 307-308, 374-376), topological form: under
`SquareBound Γ α R` with `R ≥ 0`, `0 < α < 4` and a locally finite `Γ`, the map
`(f₁,f₂,f₃,f₄) ↦ C₄(f₁,f₂,f₃,f₄)` is continuous on `(H1R d)⁴` with the product topology. -/
theorem continuous_C4 {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha4 : alpha < 4) :
    Continuous (fun x : H1R d × H1R d × H1R d × H1R d =>
      C4 Γ (fn x.1) (fn x.2.1) (fn x.2.2.1) (fn x.2.2.2)) := by
  refine continuous_iff_seqContinuous.2 fun u x hu => ?_
  have c1 := h1Tendsto_of_tendsto ((continuous_fst.tendsto x).comp hu)
  have c2 := h1Tendsto_of_tendsto (((continuous_fst.comp continuous_snd).tendsto x).comp hu)
  have c3 := h1Tendsto_of_tendsto
    (((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto x).comp hu)
  have c4 := h1Tendsto_of_tendsto
    (((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto x).comp hu)
  exact SpatialFourLinear.C4_tendsto hB hR0 ha0 ha4 (fun n => isH1Pair _)
    (fun n => isH1Pair _) (fun n => isH1Pair _) (fun n => isH1Pair _) (isH1Pair _)
    (isH1Pair _) (isH1Pair _) (isH1Pair _) c1 c2 c3 c4

/-- **Continuity of the square pairings** (TeX lines 375-376): under the hypotheses of
`continuous_C4`, `(f, h) ↦ B_Γ(f², h²)` (real value of the physical pairing) is continuous on
`H1R d × H1R d`; at `h = f` this is `A_sp`. -/
theorem continuous_sqPair_toReal {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha4 : alpha < 4) :
    Continuous (fun x : H1R d × H1R d =>
      (pairing Γ (zE fun y => fn x.1 y ^ 2) (zE fun y => fn x.2 y ^ 2)).toReal) := by
  have e : (fun x : H1R d × H1R d =>
      (pairing Γ (zE fun y => fn x.1 y ^ 2) (zE fun y => fn x.2 y ^ 2)).toReal) =
      (fun x : H1R d × H1R d × H1R d × H1R d =>
        C4 Γ (fn x.1) (fn x.2.1) (fn x.2.2.1) (fn x.2.2.2)) ∘
        (fun x : H1R d × H1R d => (x.1, x.1, x.2, x.2)) := by
    funext x
    exact SpatialFourLinear.pairing_toReal_eq_C4 (Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _)
  rw [e]
  exact (continuous_C4 hB hR0 ha0 ha4).comp (by fun_prop)

/-- **Continuity of `Q`** (`L:occupation-raw-square`, `notes/integrated_occupation_ceiling.tex`
lines 24-28, proof 64-66): under `SquareBound S.Γ α R` (`R ≥ 0`, `0 < α < 4`) the map
`p ↦ Q(p)` (`OccupationCompletion.Q`) is continuous from `H1R d` to `H_sp`. -/
theorem continuous_Q (S : OccupationCompletion.SpData d) {alpha R : ℝ}
    (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha4 : alpha < 4) :
    Continuous (fun p : H1R d => OccupationCompletion.Q S (fn p)) :=
  continuous_iff_seqContinuous.2 fun _ _ hu =>
    OccupationCompletion.tendsto_Q_of_H1 hB hR0 ha0 ha4 (fun _ => isH1Pair _) (isH1Pair _)
      (h1Tendsto_of_tendsto hu)

/-! ### The wrappers -/

/-- **`P:spatial-four-linear`, every conclusion** (`integrated_spatial_occupation.tex` lines
297-315, proof 317-398), under the section's standing assumptions (lines 4-10: `H:homog` with
`a = α₀`, `Γ ≠ 0`), with no supplied input: the conclusions of
`SpatialOccupationL7Completed.spatial_four_linear_paper_completed` for `H¹` pairs
(`E:spatial-homogeneous-bound`; finiteness and `E:spatial-square-CS`; `E:spatial-four-linear` with
absolute convergence; the sequential form of joint continuity; `R_sp = R_0`; `A_sp(f) > 0` for
nonzero `f`), and, on the space `H¹ = H1R d` whose topology is Mathlib's `H^{1}` topology
(`toMH1` an embedding), the topological joint continuity of `C₄` on `(H¹)⁴` and the continuity of
the square pairings. -/
theorem spatial_four_linear_whole_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g →
      pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2) ≤
        ENNReal.ofReal (SpatialSmoothRatio.R0 Γ alpha * Nnorm alpha f g ^ 4)) ∧
    (∀ (f h : Rd d → ℝ) (g k : Rd d → Rd d), IsH1Pair f g → IsH1Pair h k →
      pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) < ⊤ ∧
      0 ≤ (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ≤
        Real.sqrt ((pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal *
          (pairing Γ (zE fun x => h x ^ 2) (zE fun x => h x ^ 2)).toReal)) ∧
    (∀ (f₁ f₂ f₃ f₄ : Rd d → ℝ) (g₁ g₂ g₃ g₄ : Rd d → Rd d), IsH1Pair f₁ g₁ →
      IsH1Pair f₂ g₂ → IsH1Pair f₃ g₃ → IsH1Pair f₄ g₄ →
      ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (SpatialSmoothRatio.R0 Γ alpha * (Nnorm alpha f₁ g₁ *
          Nnorm alpha f₂ g₂ * Nnorm alpha f₃ g₃ * Nnorm alpha f₄ g₄)) ∧
      Integrable (fun p : Rd d × Rd d => f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))
        (pairMeasure Γ)) ∧
    (∀ (u₁ u₂ u₃ u₄ : ℕ → Rd d → ℝ) (v₁ v₂ v₃ v₄ : ℕ → Rd d → Rd d)
      (f₁ f₂ f₃ f₄ : Rd d → ℝ) (g₁ g₂ g₃ g₄ : Rd d → Rd d),
      (∀ n, IsH1Pair (u₁ n) (v₁ n)) → (∀ n, IsH1Pair (u₂ n) (v₂ n)) →
      (∀ n, IsH1Pair (u₃ n) (v₃ n)) → (∀ n, IsH1Pair (u₄ n) (v₄ n)) →
      IsH1Pair f₁ g₁ → IsH1Pair f₂ g₂ → IsH1Pair f₃ g₃ → IsH1Pair f₄ g₄ →
      H1Tendsto u₁ v₁ f₁ g₁ → H1Tendsto u₂ v₂ f₂ g₂ → H1Tendsto u₃ v₃ f₃ g₃ →
      H1Tendsto u₄ v₄ f₄ g₄ →
      Tendsto (fun n => C4 Γ (u₁ n) (u₂ n) (u₃ n) (u₄ n)) atTop (𝓝 (C4 Γ f₁ f₂ f₃ f₄))) ∧
    SpatialFourLinear.Rsp Γ alpha = SpatialSmoothRatio.R0 Γ alpha ∧
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g → ¬ f =ᵐ[volume] 0 →
      0 < pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)) ∧
    IsEmbedding (toMH1 (d := d)) ∧
    Continuous (fun x : H1R d × H1R d × H1R d × H1R d =>
      C4 Γ (fn x.1) (fn x.2.1) (fn x.2.2.1) (fn x.2.2.2)) ∧
    Continuous (fun x : H1R d × H1R d =>
      (pairing Γ (zE fun y => fn x.1 y ^ 2) (zE fun y => fn x.2 y ^ 2)).toReal) := by
  obtain ⟨-, ha0, ha2, -, -, hR0, hB⟩ :=
    SpatialFourLinear.squareBound_R0 hH hΓ (H1Density.h1TestDense d)
  have := hH.Γ_radon
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    SpatialOccupationL7Completed.spatial_four_linear_paper_completed hH hΓ
  exact ⟨h1, h2, h3, h4, h5, h6, isEmbedding_toMH1,
    continuous_C4 hB hR0.le ha0 (by linarith), continuous_sqPair_toReal hB hR0.le ha0 (by linarith)⟩

/-- **Topological continuity of `Q` in `L:occupation-raw-square`**
(`notes/integrated_occupation_ceiling.tex` lines 24-28, proof 64-66), under the standing
assumptions of that section (`H:homog` with `a = α₀`, `Γ ≠ 0`, lines 4-21): `Q : H¹ → H_sp` is
continuous on `H1R d` (Mathlib's `H^{1}` topology by `isEmbedding_toMH1`). -/
theorem occupation_raw_square_continuous_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    Continuous (fun p : H1R d =>
      OccupationCompletion.Q (OccupationCompletion.SpData.ofHomog hH) (fn p)) := by
  obtain ⟨-, ha0, ha2, -, -, hR0, hB⟩ :=
    SpatialFourLinear.squareBound_R0 hH hΓ (H1Density.h1TestDense d)
  exact continuous_Q (OccupationCompletion.SpData.ofHomog hH) hB hR0.le ha0 (by linarith)

end StratonovichHAMSecondMoment.ClassOH1
