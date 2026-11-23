module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Discharge of the supplied input `SourceTube.TubeAttained` at the manuscript's
tubes: the first sentence and the first identity of `E:tube-attained-radius` in
`L:tube-closed-geometry` (Compact images and attained tube radii) of
`notes/integrated_gaussian_tubes.tex`, TeX lines 150-165 (statement) and
167-193 (proof begins at 167; Step 1 174-193) at revision edf7085f (book 1.1.3).

Public results.
1. `isClosed_image_closedBall`: a bounded linear map from a real Hilbert space
   sends every closed ball to a closed set.
2. `isCompact_image_closedBall_of_isCompactOperator`: a compact operator from a
   real Hilbert space sends every closed ball to a compact set (TeX lines
   176-181, "including closedness of the image").
3. `tubeAttained_add_image`: abstract tubes `A + M(B̄_H(r))`, `A` closed, every
   `M(B̄_H(r))` compact, satisfy `TubeAttained` (TeX lines 182-193).
4. `tubeAttained_paperTube`: `TubeAttained (paperTube P X M)` for a compact `M`
   on a complete real inner product space.
5. `tube_closed_geometry_closed_paper`: the first sentence and first identity
   of `E:tube-attained-radius` with the manuscript's hypotheses (nothing
   supplied); `lowerSemicontinuous_tubeRadius_paperTube`: the radius is lower
   semicontinuous (TeX lines 164 and 192-193).
6. `tube_rayleigh_transfer_paper_l21`: `P:tube-rayleigh-transfer`, nonzero law,
   with only `TubeTail` supplied.

Route difference (disclosed).  The TeX (lines 176-181) proves closedness of
`M_δ(B̄_H(r))` through weakly convergent subsequences ("diagonal orthonormal
coordinates and Fatou") and the compactness of `M_δ`, for separable `H`.  Here
closedness is proved for every bounded `M` on a complete real inner product
space, without separability: through the Riesz map, the closed ball of `H` is
the weak-star closed ball of its dual, compact by Banach-Alaoglu; `M` is
continuous from it to the weak topology of `𝔅`, which is Hausdorff
(Hahn-Banach); so the image is weakly compact, hence weakly closed, hence norm
closed.  Compactness of `M` then gives compactness of the image.  The
least-radius attainment (TeX lines 186-192) is proved by rescaling a
near-optimal control `h ∈ H` into the ball of radius `r` and using the
closedness of `T_r`, instead of a weak limit of the points `h_j`; the
conclusion is the same.  Neither the nonzero law nor the Gaussianity of `X` is
used for this part of the lemma (they enter only the tail, Step 2).
-/

public import Mathlib
public import StratonovichHAMSecondMoment.SourceTube

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Pointwise

namespace StratonovichHAMSecondMoment.SourceTubeAttained

open StratonovichHAMSecondMoment.SourceTube

/-! ### Closed and compact images of Hilbert balls -/

section Images

variable {𝔅 : Type*} [NormedAddCommGroup 𝔅] [NormedSpace ℝ 𝔅]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Auxiliary (the weak-to-weak continuity of `M` through the Riesz map): for a
continuous linear functional `ℓ` on `𝔅`, `ℓ (M (R⁻¹ φ)) = φ (R⁻¹ (ℓ ∘ M))`,
with `R` the Riesz map of `H`. -/
theorem apply_toDual_symm (M : H →L[ℝ] 𝔅) (ℓ : StrongDual ℝ 𝔅) (φ : StrongDual ℝ H) :
    ℓ (M ((InnerProductSpace.toDual ℝ H).symm φ)) =
      φ ((InnerProductSpace.toDual ℝ H).symm (ℓ.comp M)) := by
  rw [← ContinuousLinearMap.comp_apply, ← InnerProductSpace.toDual_symm_apply,
    real_inner_comm, InnerProductSpace.toDual_symm_apply]

/-- A bounded linear map from a complete real inner product space sends every
closed ball to a closed set (TeX lines 176-181, closedness part; route through
Banach-Alaoglu and the Hausdorff weak topology of `𝔅`, see the module
docstring; neither separability nor compactness of `M` is needed). -/
theorem isClosed_image_closedBall (M : H →L[ℝ] 𝔅) (r : ℝ) :
    IsClosed (M '' closedBall (0 : H) r) := by
  set R := InnerProductSpace.toDual ℝ H with hR
  set S : Set (WeakDual ℝ H) := WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ H) r
  have hS : IsCompact S := WeakDual.isCompact_closedBall 0 r
  let g : WeakDual ℝ H → WeakSpace ℝ 𝔅 := fun φ =>
    toWeakSpace ℝ 𝔅 (M (R.symm (WeakDual.toStrongDual φ)))
  have hg : Continuous g := by
    apply WeakBilin.continuous_of_continuous_eval
    intro ℓ
    have e : (fun φ : WeakDual ℝ H => (topDualPairing ℝ 𝔅).flip (g φ) ℓ) =
        fun φ : WeakDual ℝ H => φ (R.symm (ℓ.comp M)) := by
      funext φ
      exact apply_toDual_symm M ℓ (WeakDual.toStrongDual φ)
    rw [e]
    exact WeakDual.eval_continuous _
  have hc : IsClosed (g '' S) := (hS.image hg).isClosed
  have hpre : M '' closedBall (0 : H) r = toWeakSpaceCLM ℝ 𝔅 ⁻¹' (g '' S) := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨WeakDual.toStrongDual.symm (R h), ?_, ?_⟩
      · simp only [S, Set.mem_preimage, mem_closedBall_zero_iff, LinearEquiv.apply_symm_apply,
          LinearIsometryEquiv.norm_map]
        simpa using hh
      · simp only [g, LinearEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
        rfl
    · rintro ⟨φ, hφ, hgy⟩
      refine ⟨R.symm (WeakDual.toStrongDual φ), ?_, hgy⟩
      have hφ' : ‖WeakDual.toStrongDual φ‖ ≤ r := by simpa [S] using hφ
      simpa [LinearIsometryEquiv.norm_map] using hφ'
  rw [hpre]
  exact hc.preimage (toWeakSpaceCLM ℝ 𝔅).continuous

/-- A compact operator from a complete real inner product space sends every
closed ball to a compact set (TeX lines 176-181: "A compact map from a
separable Hilbert space sends a closed bounded ball to a compact set, including
closedness of the image"; separability is not needed). -/
theorem isCompact_image_closedBall_of_isCompactOperator (M : H →L[ℝ] 𝔅)
    (hM : IsCompactOperator M) (r : ℝ) :
    IsCompact (M '' closedBall (0 : H) r) := by
  have h := hM.isCompact_closure_image_closedBall (f := (M : H →ₗ[ℝ] 𝔅)) r
  rwa [ContinuousLinearMap.coe_coe, (isClosed_image_closedBall M r).closure_eq] at h

end Images

/-! ### Abstract tubes `A + M(B̄_H(r))` -/

section AbstractTube

variable {𝔅 : Type*} [NormedAddCommGroup 𝔅] [NormedSpace ℝ 𝔅]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Auxiliary: closed base plus compact image is closed (TeX lines 181-184). -/
theorem isClosed_add_image {A : Set 𝔅} (hA : IsClosed A) (M : H →L[ℝ] 𝔅)
    (hK : ∀ r : ℝ, 0 ≤ r → IsCompact (M '' closedBall (0 : H) r)) {r : ℝ} (hr : 0 ≤ r) :
    IsClosed (A + M '' closedBall (0 : H) r) :=
  hA.add_right_of_isCompact (hK r hr)

/-- Auxiliary: the tubes increase with the radius. -/
theorem add_image_mono (A : Set 𝔅) (M : H →L[ℝ] 𝔅) {r s : ℝ} (h : r ≤ s) :
    A + M '' closedBall (0 : H) r ⊆ A + M '' closedBall (0 : H) s :=
  add_subset_add_left (image_mono (closedBall_subset_closedBall h))

/-- Auxiliary (TeX lines 186-191, by rescaling instead of a weak limit): if
`x ∈ T_{r+ε}` for every `ε > 0`, then `x ∈ T_r`. -/
theorem mem_add_image_of_forall {A : Set 𝔅} (hA : IsClosed A) (M : H →L[ℝ] 𝔅)
    (hK : ∀ r : ℝ, 0 ≤ r → IsCompact (M '' closedBall (0 : H) r)) {r : ℝ} (hr : 0 ≤ r)
    {x : 𝔅} (hx : ∀ ε > 0, x ∈ A + M '' closedBall (0 : H) (r + ε)) :
    x ∈ A + M '' closedBall (0 : H) r := by
  rw [← (isClosed_add_image hA M hK hr).closure_eq, Metric.mem_closure_iff]
  intro δ hδ
  set c := ‖M‖ + 1 with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨a, ha, y, ⟨h, hh, rfl⟩, rfl⟩ := hx (δ / (2 * c)) (by positivity)
  have hh' : ‖h‖ ≤ r + δ / (2 * c) := by simpa using hh
  set t : ℝ := r / (r + δ / (2 * c))
  have hden : 0 < r + δ / (2 * c) := by positivity
  have ht0 : 0 ≤ t := div_nonneg hr hden.le
  have ht1 : t ≤ 1 := (div_le_one hden).2 (by linarith [show 0 < δ / (2 * c) by positivity])
  refine ⟨a + M (t • h), ⟨a, ha, M (t • h), ⟨t • h, ?_, rfl⟩, rfl⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht0]
    calc t * ‖h‖ ≤ t * (r + δ / (2 * c)) := mul_le_mul_of_nonneg_left hh' ht0
      _ = r := div_mul_cancel₀ r hden.ne'
  · rw [dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub]
    have e : h - t • h = (1 - t) • h := by rw [sub_smul, one_smul]
    have h1t : (1 - t) * (r + δ / (2 * c)) = δ / (2 * c) := by
      simp only [t, sub_mul, one_mul, div_mul_cancel₀ r hden.ne']; ring
    calc ‖M (h - t • h)‖ ≤ ‖M‖ * ‖h - t • h‖ := M.le_opNorm _
      _ = ‖M‖ * ((1 - t) * ‖h‖) := by rw [e, norm_smul, Real.norm_of_nonneg (by linarith)]
      _ ≤ ‖M‖ * ((1 - t) * (r + δ / (2 * c))) := by gcongr
      _ = ‖M‖ * (δ / (2 * c)) := by rw [h1t]
      _ ≤ c * (δ / (2 * c)) := by gcongr; linarith
      _ = δ / 2 := by field_simp
      _ < δ := by linarith

/-- Closed tubes and least-radius attainment for abstract tubes
`T_r = A + M(B̄_H(r))` with `A` closed and every `M(B̄_H(r))`, `r ≥ 0`, compact
(TeX lines 182-193). -/
theorem tubeAttained_add_image {A : Set 𝔅} (hA : IsClosed A) (M : H →L[ℝ] 𝔅)
    (hK : ∀ r : ℝ, 0 ≤ r → IsCompact (M '' closedBall (0 : H) r)) :
    TubeAttained (fun r => A + M '' closedBall (0 : H) r) := by
  intro r hr
  refine ⟨isClosed_add_image hA M hK hr, Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · apply mem_add_image_of_forall hA M hK hr
    intro ε hε
    simp only [mem_ofPred_eq, tubeRadius] at hx
    have : ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : x ∈ A + M '' closedBall (0 : H) s), ENNReal.ofReal s <
        ENNReal.ofReal (r + ε) := by
      refine hx.trans_lt ?_
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
      linarith
    simp only [iInf_lt_iff] at this
    obtain ⟨s, hs, hxs, hlt⟩ := this
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)] at hlt
    exact add_image_mono A M hlt.le hxs
  · simp only [mem_ofPred_eq, tubeRadius]
    exact iInf₂_le_of_le r hr (iInf_le_of_le hx le_rfl)

end AbstractTube

/-! ### The manuscript's tubes -/

section PaperTube

variable {𝔅 : Type*} [NormedAddCommGroup 𝔅] [NormedSpace ℝ 𝔅]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Auxiliary: the base set `A_δ = {x ∈ E₀ : ‖x‖ ≤ b_δ}` is closed (TeX line 155). -/
theorem isClosed_paperBase {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → 𝔅)
    (M : H →L[ℝ] 𝔅) :
    IsClosed {x ∈ closure (Set.range M) | ‖x‖ ≤ 2 * ∫ ω, ‖X ω‖ ∂P} :=
  isClosed_closure.inter (isClosed_le continuous_norm continuous_const)

/-- `TubeAttained` at the manuscript's tubes `T_r = A_δ + M_δ(B̄_H(r))` (TeX lines
152-163 (tubes 154-156; 158; 161), proved 174-193): for a compact `M` on a complete real inner
product space, every `T_r`, `r ≥ 0`, is closed and `{d_δ ≤ r} = T_r`. -/
theorem tubeAttained_paperTube [CompleteSpace H] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → 𝔅) (M : H →L[ℝ] 𝔅) (hM : IsCompactOperator M) :
    TubeAttained (paperTube P X M) :=
  tubeAttained_add_image (isClosed_paperBase P X M) M
    fun r _ => isCompact_image_closedBall_of_isCompactOperator M hM r

/-- `L:tube-closed-geometry` (`notes/integrated_gaussian_tubes.tex`, TeX lines
150-165 at revision edf7085f, proof lines 167-193, Step 1 174-193), the first sentence and the
first identity of `E:tube-attained-radius`, with the manuscript's hypotheses
(nothing supplied): `𝔅` real separable Banach with its Borel sets, `H` real
separable Hilbert, `M_δ` compact, `0 < δ < 1`, `X` measurable with
`E‖X‖² < ∞` and nonzero law.  Every `T_r`, `r ≥ 0`, is closed and
`{d_δ ≤ r} = T_r`.  The Gaussian tail (second identity) is not part of this
statement.  Only `CompleteSpace H` and the compactness of `M` are used. -/
theorem tube_closed_geometry_closed_paper [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [TopologicalSpace.SeparableSpace 𝔅] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (M : H →L[ℝ] 𝔅) (hM : IsCompactOperator M) (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1)
    (X : Ω → 𝔅) (_hX : AEMeasurable X P) (_hX2 : MemLp X 2 P)
    (_hlaw : ¬ ∀ᵐ ω ∂P, X ω = 0) :
    ∀ r : ℝ, 0 ≤ r → IsClosed (paperTube P X M r) ∧
      {x | tubeRadius (paperTube P X M) x ≤ ENNReal.ofReal r} = paperTube P X M r :=
  tubeAttained_paperTube P X M hM

/-- `L:tube-closed-geometry`, "In particular, `d_δ` is lower semicontinuous"
(TeX lines 164 and 192-193, "Closed sublevels give lower semicontinuity"), for
a compact `M` on a complete real inner product space. -/
theorem lowerSemicontinuous_tubeRadius_paperTube [CompleteSpace H] {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → 𝔅) (M : H →L[ℝ] 𝔅)
    (hM : IsCompactOperator M) :
    LowerSemicontinuous (tubeRadius (paperTube P X M)) := by
  have hT := tubeAttained_paperTube P X M hM
  refine lowerSemicontinuous_iff_isClosed_preimage.2 fun y => ?_
  induction y using ENNReal.recTopCoe with
  | top => simp
  | coe q =>
    have hq : ((q : ℝ≥0∞)) = ENNReal.ofReal (q : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    rw [hq]
    change IsClosed {x | tubeRadius (paperTube P X M) x ≤ ENNReal.ofReal q}
    rw [(hT q q.2).2]
    exact (hT q q.2).1

/-- `P:tube-rayleigh-transfer` (`notes/integrated_gaussian_tubes.tex`, TeX lines
225-271 at revision edf7085f), nonzero law, with the manuscript's hypotheses and
only the Gaussian tail `TubeTail` of `L:tube-closed-geometry` supplied (the
input `TubeAttained` of `SourceTube.tube_rayleigh_transfer_paper` is discharged
by `tubeAttained_paperTube`).  Same hypotheses and conclusion as
`tube_rayleigh_transfer_paper`, without `hAtt`. -/
theorem tube_rayleigh_transfer_paper_l21 [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [TopologicalSpace.SeparableSpace 𝔅] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (M : H →L[ℝ] 𝔅) (hM : IsCompactOperator M) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (X : Ω → 𝔅) (hX : AEMeasurable X P) (hX2 : MemLp X 2 P)
    (hlaw : ¬ ∀ᵐ ω ∂P, X ω = 0)
    (hTail : TubeTail P X (paperTube P X M) δ)
    (F : 𝔅 → ℝ) (hF : Measurable F) (G : ℝ → ℝ) (hGm : Measurable G)
    (hG : MonotoneOn G (Ici 0))
    (hFG : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ paperTube P X M r, F x ≤ G r) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (F (X ω) / δ)) ∂P ≤
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) :=
  tube_rayleigh_transfer_paper M hM δ hδ hδ1 X hX hX2 hlaw
    (tubeAttained_paperTube P X M hM) hTail F hF G hGm hG hFG

end PaperTube

end StratonovichHAMSecondMoment.SourceTubeAttained
