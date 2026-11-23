module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-B2 (approved by Le on 2026-11-20): `P:cameron-spatial-map`, `E` part.  The
objects are those of the frozen interface `StratonovichHAMSecondMoment.CameronInterface`
(commit 1e9c544); nothing there is changed.  The outputs of items A1 (`uniform_cutoff`,
`sobolev_embed`), A2 (`cameron_fractional_products`) and B1 (`cutoffCompact`) are taken as
hypotheses with exactly their frozen signatures; they are discharged at integration.

TeX anchors (revision 0788ddee, book 1.1.0, read with `git show 0788ddee:notes/...`; the same
line numbers at edf7085f, book 1.1.3):
* `integrated_cameron_mean.tex` lines 15-21 (the radius `R > 0` and `η_R`), lines 104-119
  (`P:cameron-spatial-map`; `E:cameron-spatial-row` lines 113-118), proof lines 121-186 (Step 1
  the row 128-140; Step 2 compact row families 143-150; Step 3 compact values 152-163; Step 4
  compactness of the map 166-186);
* `integrated_uniform_mean.tex` lines 22-32 (`E:uniform-mean-row` and the rough states).

Lean proof route.
* The row `k(z,w) = P(ι η_R z₁, ι η_R Λ⁻¹ w₂)` is a bounded bilinear map `E × E → H_sp`
  (`kRowL`); `T q` is the operator with `⟪T q z, w⟫ = ⟪q, k(z,w)⟫`, `T q z = (k(z,·))† q`
  (`rieszMap`).  This is the TeX's "the row identity gives `‖T q‖ ≤ sup ‖k‖ ‖q‖`" (Step 2).
* Two rows built from spec-satisfying data (any `s`) agree on the dense test states (both are
  `rowTest`, `CameronInterface.kRow_test`), hence everywhere (`kRowL_unique`): the row identity
  holds at all states for every `α/4 < s < 1/2` (TeX Step 1, last sentence).
* On a smooth test `q`, `T q = B_E(M)` with `M` the multiplier by `m_R (Γ * q)`: physical
  Fubini (`SpatialSmoothRatio.integral_conv_mul`) and evenness of `Γ` (TeX Step 1).

Main results: `rieszMap`, `inner_rieszMap`, `kRowL_unique`, `smooth_formula`,
`meanMap`, `isSpatialMeanMap_meanMap`, `spatialRowAll_meanMap`, `spatial_mean_map_at`,
`spatial_mean_map_of_one_le`.

No `sorry`, no axiom; every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronInterface
public import StratonovichHAMSecondMoment.CompactOperatorFoundation
public import StratonovichHAMSecondMoment.UniformELift

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff RealInnerProductSpace Real SchwartzMap

namespace StratonovichHAMSecondMoment.CameronSpatial

open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (IsTestFunction)
open OccupationCompletion (SpData Hsp toHsp)
open VariationalDilation (conv)
open SpatialFourierBound (spatialPair)
open UniformMeanInterface
open CameronInterface

variable {d : ℕ} {S : SpData d}

/-! ### The row as a bounded bilinear map -/

/-- The left factor `z ↦ ι (η_R z₁)` of the row. -/
def leftL {s : ℝ} (ι : Hsob d (1 / 2) →L[ℝ] Hsob d s)
    (Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)) : E d →L[ℝ] Hsob d s :=
  ι ∘L Lη ∘L hhalfEquiv.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousLinearMap.fst ℝ (Hhalf d) (Hmhalf d) ∘L (eEquiv (d := d)).toContinuousLinearMap

/-- The right factor `w ↦ ι (η_R Λ⁻¹ w₂)` of the row. -/
def rightL {s : ℝ} (ι : Hsob d (1 / 2) →L[ℝ] Hsob d s)
    (Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)) : E d →L[ℝ] Hsob d s :=
  ι ∘L Lη ∘L hhalfEquiv.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (lam (d := d)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousLinearMap.snd ℝ (Hhalf d) (Hmhalf d) ∘L (eEquiv (d := d)).toContinuousLinearMap

/-- **The row `k(z,w) = P(ι η_R z₁, ι η_R Λ⁻¹ w₂)` as a bounded bilinear map** `E × E → H_sp`
(`E:uniform-mean-row`, `integrated_uniform_mean.tex` lines 22-32 at revision edf7085f (book
1.1.3)). -/
def kRowL (S : SpData d) {s : ℝ} (P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S)
    (ι : Hsob d (1 / 2) →L[ℝ] Hsob d s) (Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)) :
    E d →L[ℝ] E d →L[ℝ] Hsp S :=
  P.bilinearComp (leftL ι Lη) (rightL ι Lη)

/-- Auxiliary: `kRowL` is `kRow`. -/
theorem kRowL_apply {s : ℝ} (P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S)
    (ι : Hsob d (1 / 2) →L[ℝ] Hsob d s) (Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2))
    (z w : E d) : kRowL S P ι Lη z w = kRow S P ι Lη z w := rfl

/-! ### The operator of a bounded bilinear row -/

section Riesz

variable {X Y H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Auxiliary: the linear map `q ↦ (z ↦ (B z)† q)`. -/
def rieszLin (B : X →L[ℝ] Y →L[ℝ] H) : H →ₗ[ℝ] X →ₗ[ℝ] Y where
  toFun q :=
    { toFun := fun z => ContinuousLinearMap.adjoint (B z) q
      map_add' := fun z z' => by simp [map_add]
      map_smul' := fun c z => by simp [map_smul] }
  map_add' q q' := by ext z; simp
  map_smul' c q := by ext z; simp

/-- **The operator of a bounded row** `B : X × Y → H` with `‖B z w‖ ≤ C ‖z‖ ‖w‖`:
`T q z = (B z)† q`, so that `⟪T q z, w⟫ = ⟪q, B z w⟫` (`inner_rieszMap`) and `‖T‖ ≤ C`
(`integrated_cameron_mean.tex` at revision edf7085f (book 1.1.3): the row identity
`E:cameron-spatial-row`, lines 113-118, and the bound `‖T_sp q‖ ≤ sup_{k ∈ 𝓛} ‖k‖ ‖q‖` of
Step 2 (144-156), lines 153-154; the Riesz representation `(B z)† q` is the Lean
realization). -/
def rieszMap (B : X →L[ℝ] Y →L[ℝ] H) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ z w, ‖B z w‖ ≤ C * ‖z‖ * ‖w‖) : H →L[ℝ] (X →L[ℝ] Y) :=
  (rieszLin B).mkContinuous₂ C fun q z => by
    change ‖ContinuousLinearMap.adjoint (B z) q‖ ≤ C * ‖q‖ * ‖z‖
    have hBz : ‖B z‖ ≤ C * ‖z‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => hB z w
    calc ‖ContinuousLinearMap.adjoint (B z) q‖ ≤ ‖ContinuousLinearMap.adjoint (B z)‖ * ‖q‖ :=
          (ContinuousLinearMap.adjoint (B z)).le_opNorm q
      _ = ‖B z‖ * ‖q‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ C * ‖z‖ * ‖q‖ := by gcongr
      _ = C * ‖q‖ * ‖z‖ := by ring

/-- Auxiliary: `T q z = (B z)† q`. -/
theorem rieszMap_apply (B : X →L[ℝ] Y →L[ℝ] H) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ z w, ‖B z w‖ ≤ C * ‖z‖ * ‖w‖) (q : H) (z : X) :
    rieszMap B hC hB q z = ContinuousLinearMap.adjoint (B z) q := rfl

/-- **The row identity of `rieszMap`**: `⟪T q z, w⟫ = ⟪q, B z w⟫`. -/
theorem inner_rieszMap (B : X →L[ℝ] Y →L[ℝ] H) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ z w, ‖B z w‖ ≤ C * ‖z‖ * ‖w‖) (q : H) (z : X) (w : Y) :
    ⟪rieszMap B hC hB q z, w⟫ = ⟪q, B z w⟫ := by
  rw [rieszMap_apply, ContinuousLinearMap.adjoint_inner_left]

/-- Auxiliary: `‖T x‖ ≤ δ` as soon as the row pairing of `x` is bounded by `δ ‖z‖ ‖w‖`. -/
theorem norm_rieszMap_apply_le (B : X →L[ℝ] Y →L[ℝ] H) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ z w, ‖B z w‖ ≤ C * ‖z‖ * ‖w‖) (x : H) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ z w, |⟪x, B z w⟫| ≤ δ * ‖z‖ * ‖w‖) : ‖rieszMap B hC hB x‖ ≤ δ := by
  refine ContinuousLinearMap.opNorm_le_bound _ hδ fun z => ?_
  set v := rieszMap B hC hB x z
  have h1 : ‖v‖ ^ 2 ≤ δ * ‖z‖ * ‖v‖ := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪rieszMap B hC hB x z, v⟫ ≤ _
    rw [inner_rieszMap]
    exact (le_abs_self _).trans (h z v)
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

end Riesz

/-- Auxiliary: the row of spec data is bounded, `‖k(z,w)‖ ≤ A ‖ι η_R‖ ‖ι η_R Λ⁻¹‖ ‖z‖ ‖w‖`. -/
theorem norm_kRowL_le {s A : ℝ} {P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S}
    (hPA : ∀ u v, ‖P u v‖ ≤ A * ‖u‖ * ‖v‖) (hA : 0 ≤ A) (ι : Hsob d (1 / 2) →L[ℝ] Hsob d s)
    (Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)) (z w : E d) :
    ‖kRowL S P ι Lη z w‖ ≤ (A * ‖leftL ι Lη‖ * ‖rightL ι Lη‖) * ‖z‖ * ‖w‖ := by
  change ‖P (leftL ι Lη z) (rightL ι Lη w)‖ ≤ _
  calc ‖P (leftL ι Lη z) (rightL ι Lη w)‖ ≤ A * ‖leftL ι Lη z‖ * ‖rightL ι Lη w‖ := hPA _ _
    _ ≤ A * (‖leftL ι Lη‖ * ‖z‖) * (‖rightL ι Lη‖ * ‖w‖) := by
        gcongr
        · exact (leftL ι Lη).le_opNorm z
        · exact (rightL ι Lη).le_opNorm w
    _ = (A * ‖leftL ι Lη‖ * ‖rightL ι Lη‖) * ‖z‖ * ‖w‖ := by ring

/-- **The spatial mean map of spec data** `(P, ι, Lη)` with product bound `A`. -/
def meanMap (S : SpData d) {s A : ℝ} (P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S)
    (hPA : ∀ u v, ‖P u v‖ ≤ A * ‖u‖ * ‖v‖) (hA : 0 ≤ A) (ι : Hsob d (1 / 2) →L[ℝ] Hsob d s)
    (Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)) : Hsp S →L[ℝ] (E d →L[ℝ] E d) :=
  rieszMap (kRowL S P ι Lη) (by positivity) (norm_kRowL_le hPA hA ι Lη)

/-- **The row identity of `meanMap`**: `⟪T q z, w⟫ = ⟪q, k(z,w)⟫`. -/
theorem inner_meanMap {s A : ℝ} {P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S}
    (hPA : ∀ u v, ‖P u v‖ ≤ A * ‖u‖ * ‖v‖) (hA : 0 ≤ A) (ι : Hsob d (1 / 2) →L[ℝ] Hsob d s)
    (Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)) (q : Hsp S) (z w : E d) :
    ⟪meanMap S P hPA hA ι Lη q z, w⟫ = ⟪q, kRow S P ι Lη z w⟫ :=
  inner_rieszMap _ _ _ q z w

/-! ### Uniqueness of the row from the dense test states -/

/-- Auxiliary: two bounded bilinear maps `E × E → H_sp` agreeing on the test states
`z = (f, z₂)`, `w = (w₁, Λ g)` are equal (density of tests in `H^{1/2}`). -/
theorem bilin_eq_of_testStates {B B' : E d →L[ℝ] E d →L[ℝ] Hsp S}
    (h : ∀ f g : Rd d → ℝ, IsTestFunction f → IsTestFunction g → ∀ (z₂ : Hmhalf d) (w₁ : Hhalf d),
      B (toE (toHhalf f) z₂) (toE w₁ (lam (toHhalf g))) =
        B' (toE (toHhalf f) z₂) (toE w₁ (lam (toHhalf g)))) : B = B' := by
  set D := B - B' with hD
  have hz : ∀ z ∈ {z : E d | ∃ f z₂, IsTestFunction f ∧ z = toE (toHhalf f) z₂}, D z = 0 := by
    rintro _ ⟨f, z₂, hf, rfl⟩
    have hcl : IsClosed {w : E d | D (toE (toHhalf f) z₂) w = 0} :=
      isClosed_eq (D (toE (toHhalf f) z₂)).continuous continuous_const
    have hsub := closure_minimal (s := {w : E d | ∃ w₁ g, IsTestFunction g ∧
      w = toE w₁ (lam (toHhalf g))}) (fun w hw => by
        obtain ⟨w₁, g, hg, rfl⟩ := hw
        change (B - B') _ _ = 0
        rw [sub_apply, sub_apply, h f g hf hg, sub_self])
      hcl
    rw [(PositiveRawMean.dense_dualStates PositiveRawMean.um0Facts).closure_eq] at hsub
    exact ContinuousLinearMap.ext fun w => hsub (mem_univ w)
  have hcl : IsClosed {z : E d | D z = 0} := isClosed_eq D.continuous continuous_const
  have hsub := closure_minimal hz hcl
  rw [(PositiveRawMean.dense_testStates PositiveRawMean.um0Facts).closure_eq] at hsub
  have hD0 : D = 0 := ContinuousLinearMap.ext fun z => hsub (mem_univ z)
  exact sub_eq_zero.1 hD0

/-- **Uniqueness of the row**: rows built from spec-satisfying product maps, embeddings and
cutoff multipliers, at any two exponents `s, s'`, are the same bilinear map (both restrict to
`rowTest` on the dense test states). -/
theorem kRowL_unique {η : CutoffProfile d} {R s s' : ℝ}
    {P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S} {ι : Hsob d (1 / 2) →L[ℝ] Hsob d s}
    {Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)}
    {P' : Hsob d s' →L[ℝ] Hsob d s' →L[ℝ] Hsp S} {ι' : Hsob d (1 / 2) →L[ℝ] Hsob d s'}
    {Lη' : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)}
    (hP : IsFracProduct S s P) (hι : IsSobolevEmbed (1 / 2) s ι)
    (hL : IsCutoffMul (1 / 2) (1 / 2) (etaR η R) Lη)
    (hP' : IsFracProduct S s' P') (hι' : IsSobolevEmbed (1 / 2) s' ι')
    (hL' : IsCutoffMul (1 / 2) (1 / 2) (etaR η R) Lη') :
    kRowL S P ι Lη = kRowL S P' ι' Lη' := by
  refine bilin_eq_of_testStates fun f g hf hg z₂ w₁ => ?_
  rw [kRowL_apply, kRowL_apply, kRow_test hP hι hL hf hg, kRow_test hP' hι' hL' hf hg]

/-! ### The smooth-test formula -/

/-- Auxiliary: `Γ * q` is smooth for a test `q`. -/
theorem conv_contDiff {q : Rd d → ℝ} (hq : IsTestFunction q) : ContDiff ℝ ∞ (conv S.Γ q) := by
  rw [SpatialSmoothRatio.conv_eq_convolution]
  exact hq.2.contDiff_convolution_right _ (locallyIntegrable_const 1) hq.1

/-- **The smooth-test formula** (`integrated_cameron_mean.tex` Step 1, lines 128-136 at
revision edf7085f (book 1.1.3)): if `T` has the row identity on the test states, then
for a real test `q`, `T [q] = B_E(M)` with `M` the multiplier by `m_R (Γ * q)`. -/
theorem smooth_formula {η : CutoffProfile d} {R : ℝ} (hR : 0 < R)
    (T : Hsp S →L[ℝ] (E d →L[ℝ] E d))
    (hrow : ∀ (q : Hsp S) (f g : Rd d → ℝ), IsTestFunction f → IsTestFunction g →
      ∀ (z₂ : Hmhalf d) (w₁ : Hhalf d),
        ⟪T q (toE (toHhalf f) z₂), toE w₁ (lam (toHhalf g))⟫ = ⟪q, rowTest S η R f g⟫)
    {q : Rd d → ℝ} (hq : IsTestFunction q) :
    ∃ M : Hhalf d →L[ℝ] Hmhalf d, IsMultiplier (fun x => mR η R x * conv S.Γ q x) M ∧
      T (toHsp S q) = BE M := by
  set V : Rd d → ℝ := fun x => mR η R x * conv S.Γ q x with hVdef
  have hV : ContDiff ℝ ∞ V := (PositiveRawMean.mR_contDiff η R).mul (conv_contDiff hq)
  have hmc : HasCompactSupport (mR η R) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (2 * R))
      ((subset_tsupport _).trans (tsupport_mR_subset η hR))
  have hVc : HasCompactSupport V := hmc.mul_right
  obtain ⟨C, hC⟩ := hV.continuous.bounded_above_of_compact_support hVc
  obtain ⟨M, hM, -⟩ := exists_isMultiplier hV (C := C) fun x => by
    rw [← Real.norm_eq_abs]; exact hC x
  refine ⟨M, hM, ?_⟩
  -- the physical row of `q`
  have hq' : ∀ f g : Rd d → ℝ, IsTestFunction f → IsTestFunction g →
      ⟪toHsp S q, rowTest S η R f g⟫ = ∫ x, V x * f x * g x := by
    intro f g hf hg
    have hηf := isTest_smooth_mul (PositiveRawMean.etaR_contDiff η R) hf
    have hηg := isTest_smooth_mul (PositiveRawMean.etaR_contDiff η R) hg
    have hk : IsTestFunction fun x => (etaR η R x * f x) * (etaR η R x * g x) :=
      isTest_mul hηf hηg
    rw [rowTest, OccupationCompletion.inner_toHsp hq hk,
      ← SpatialFourLinear.spatialPair_comm S.even hq.1.continuous hk.1.continuous hk.2,
      ← (SpatialSmoothRatio.integral_conv_mul S.Γ hk.1.continuous hk.2 hq.1.continuous
        hq.2).2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hVdef, mR_eq]
    ring
  set D := T (toHsp S q) - BE M with hD
  have hdw : ∀ z ∈ {z : E d | ∃ f z₂, IsTestFunction f ∧ z = toE (toHhalf f) z₂},
      ∀ w ∈ {w : E d | ∃ w₁ g, IsTestFunction g ∧ w = toE w₁ (lam (toHhalf g))},
      ⟪D z, w⟫ = 0 := by
    rintro _ ⟨f, z₂, hf, rfl⟩ _ ⟨w₁, g, hg, rfl⟩
    have hVf : IsTestFunction fun x => V x * f x := ⟨hM.1.mul hf.1, hf.2.mul_left⟩
    rw [hD, sub_apply, inner_sub_left, hrow _ f g hf hg z₂ w₁,
      BE_apply, PositiveRawMean.inner_toE, inner_zero_left, zero_add, hM.2 f hf,
      inner_toHmhalf_lam hVf hg, hq' f g hf hg, sub_eq_zero]
  have hz : ∀ z ∈ {z : E d | ∃ f z₂, IsTestFunction f ∧ z = toE (toHhalf f) z₂}, D z = 0 := by
    intro z hz
    have hcl : IsClosed {w : E d | ⟪D z, w⟫ = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub := closure_minimal (fun w hw => hdw z hz w hw) hcl
    rw [(PositiveRawMean.dense_dualStates PositiveRawMean.um0Facts).closure_eq] at hsub
    exact inner_self_eq_zero.1 (hsub (mem_univ _))
  have hcl : IsClosed {z : E d | D z = 0} := isClosed_eq D.continuous continuous_const
  have hsub := closure_minimal hz hcl
  rw [(PositiveRawMean.dense_testStates PositiveRawMean.um0Facts).closure_eq] at hsub
  have hD0 : D = 0 := ContinuousLinearMap.ext fun z => hsub (mem_univ z)
  exact sub_eq_zero.1 hD0

/-! ### The spatial mean map -/

/-- **`T = meanMap` satisfies `IsSpatialMeanMap`** (test-state row and smooth-test formula),
for any spec-satisfying product map, embedding and cutoff multiplier. -/
theorem isSpatialMeanMap_meanMap {η : CutoffProfile d} {R s A : ℝ} (hR : 0 < R)
    {P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S} (hPA : ∀ u v, ‖P u v‖ ≤ A * ‖u‖ * ‖v‖)
    (hA : 0 ≤ A) {ι : Hsob d (1 / 2) →L[ℝ] Hsob d s}
    {Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)}
    (hP : IsFracProduct S s P) (hι : IsSobolevEmbed (1 / 2) s ι)
    (hL : IsCutoffMul (1 / 2) (1 / 2) (etaR η R) Lη) :
    IsSpatialMeanMap S η R (meanMap S P hPA hA ι Lη) := by
  have hrow : ∀ (q : Hsp S) (f g : Rd d → ℝ), IsTestFunction f → IsTestFunction g →
      ∀ (z₂ : Hmhalf d) (w₁ : Hhalf d),
        ⟪meanMap S P hPA hA ι Lη q (toE (toHhalf f) z₂), toE w₁ (lam (toHhalf g))⟫ =
          ⟪q, rowTest S η R f g⟫ := by
    intro q f g hf hg z₂ w₁
    rw [inner_meanMap, kRow_test hP hι hL hf hg]
  exact ⟨fun q hq => smooth_formula hR _ hrow hq, hrow⟩

/-- **The all-state row of `meanMap`** (`E:uniform-mean-row` at rough states,
`integrated_cameron_mean.tex` Step 1, lines 136-140 at revision edf7085f (book
1.1.3)), for every exponent `s'` and every spec-satisfying data at `s'`. -/
theorem spatialRowAll_meanMap {η : CutoffProfile d} {R s A : ℝ}
    {P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S} (hPA : ∀ u v, ‖P u v‖ ≤ A * ‖u‖ * ‖v‖)
    (hA : 0 ≤ A) {ι : Hsob d (1 / 2) →L[ℝ] Hsob d s}
    {Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)}
    (hP : IsFracProduct S s P) (hι : IsSobolevEmbed (1 / 2) s ι)
    (hL : IsCutoffMul (1 / 2) (1 / 2) (etaR η R) Lη) (s' : ℝ) :
    SpatialRowAll S η R s' (meanMap S P hPA hA ι Lη) := by
  intro P' ι' Lη' hP' hι' hL' q z w
  rw [inner_meanMap, ← kRowL_apply, kRowL_unique hP hι hL hP' hι' hL', kRowL_apply]

/-- Auxiliary: under `H:homog`, `α/4 < 1/2` (from `α₀ + α < 2`, `α₀ > 0`; TeX line 130-131). -/
theorem alpha_quarter_lt {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) : alpha / 4 < 1 / 2 := by
  have := hH.threshold
  have := hH.alpha0_pos
  linarith

/-- Auxiliary: the midpoint exponent `s₀ = (α/4 + 1/2)/2 ∈ (α/4, 1/2)`. -/
theorem s0_mem {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) :
    alpha / 4 < (alpha / 4 + 1 / 2) / 2 ∧ (alpha / 4 + 1 / 2) / 2 < 1 / 2 := by
  have := alpha_quarter_lt hH
  constructor <;> linarith

/-- **`P:cameron-spatial-map`, `E` part without compactness, at one radius** from a cutoff
multiplier by `η_R` on `H^{1/2}` (any bound): there is `T` with the smooth-test formula, the
test-state row, and the all-state row for every `α/4 < s < 1/2`
(`integrated_cameron_mean.tex` Step 1, lines 128-140 at revision edf7085f (book
1.1.3)). -/
theorem spatial_mean_map_at {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)} (hE : SobolevEmbedTarget d)
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s)
    (hH : HomogCovariance d alpha alpha0 Γ μ) (η : CutoffProfile d) {R : ℝ} (hR : 0 < R)
    {Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)} (hL : IsCutoffMul (1 / 2) (1 / 2) (etaR η R) Lη) :
    ∃ T : Hsp (SpData.ofHomog hH) →L[ℝ] (E d →L[ℝ] E d),
      IsSpatialMeanMap (SpData.ofHomog hH) η R T ∧
        ∀ s : ℝ, alpha / 4 < s → s < 1 / 2 → SpatialRowAll (SpData.ofHomog hH) η R s T := by
  obtain ⟨hs1, hs2⟩ := s0_mem hH
  obtain ⟨Cs, hCs0, hCs⟩ := hA2 _ hs1 hs2
  obtain ⟨P, hP, -, hPA, -⟩ := hCs alpha0 Γ μ hH
  obtain ⟨ι, hι, -⟩ := hE (1 / 2) ((alpha / 4 + 1 / 2) / 2) hs2.le
  have hA : 0 ≤ Cs ^ 2 * √(SpatialFourLinear.Rsp Γ alpha) := by positivity
  exact ⟨meanMap _ P hPA hA ι Lη, isSpatialMeanMap_meanMap hR hPA hA hP hι hL,
    fun s _ _ => spatialRowAll_meanMap hPA hA hP hι hL s⟩

/-- **`P:cameron-spatial-map`, `E` part without compactness, for every `R ≥ 1`** (the radii of
the uniform section, `integrated_uniform_mean.tex` lines 7-10 at revision edf7085f (book
1.1.3)), from the frozen outputs of A1 (`UniformCutoffTarget` at `σ = 1/2`,
`SobolevEmbedTarget`) and A2. -/
theorem spatial_mean_map_of_one_le {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hA1 : ∀ η : CutoffProfile d, UniformCutoffTarget η) (hE : SobolevEmbedTarget d)
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s)
    (hH : HomogCovariance d alpha alpha0 Γ μ) (η : CutoffProfile d) {R : ℝ} (hR : 1 ≤ R) :
    ∃ T : Hsp (SpData.ofHomog hH) →L[ℝ] (E d →L[ℝ] E d),
      IsSpatialMeanMap (SpData.ofHomog hH) η R T ∧
        ∀ s : ℝ, alpha / 4 < s → s < 1 / 2 → SpatialRowAll (SpData.ofHomog hH) η R s T := by
  obtain ⟨Lη, hL, -⟩ := hA1 η (1 / 2) R hR
  exact spatial_mean_map_at hE hA2 hH η (by linarith) hL

/-! ### Dilations of `H^{1/2}` and the cutoff at every radius -/

/-- Auxiliary: the Fourier transform of a dilation, `𝓕(φ(c·))(ξ) = c^{-d} 𝓕φ(ξ/c)`, `c > 0`. -/
theorem fourier_dil (φ : Rd d → ℝ) {c : ℝ} (hc : 0 < c) (ξ : Rd d) :
    𝓕 (fun x => (φ (c • x) : ℂ)) ξ = ((c ^ d)⁻¹ : ℝ) • 𝓕 (fun x => (φ x : ℂ)) (c⁻¹ • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Rd d)))
    (fun y : Rd d => Real.fourierChar (-⟪c⁻¹ • y, ξ⟫) • (φ y : ℂ)) c
  simp only [finrank_euclideanSpace_fin] at h
  have e1 : (fun x : Rd d => Real.fourierChar (-⟪x, ξ⟫) • (φ (c • x) : ℂ)) =
      fun x => Real.fourierChar (-⟪c⁻¹ • (c • x), ξ⟫) • (φ (c • x) : ℂ) := by
    funext x; rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rw [e1, h, abs_of_pos (by positivity)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [real_inner_smul_left, real_inner_smul_right]

/-- Auxiliary: a dilate of a test is a test. -/
theorem isTest_dil {φ : Rd d → ℝ} (hφ : IsTestFunction φ) {c : ℝ} (hc : c ≠ 0) :
    IsTestFunction fun x => φ (c • x) :=
  ⟨hφ.1.comp (contDiff_id.const_smul c), hφ.2.comp_smul hc⟩

/-- Auxiliary: the weight comparison `⟨2πcξ⟩ ≤ max(1,c) ⟨2πξ⟩`. -/
theorem weight_dil_le {c : ℝ} (hc : 0 < c) (ζ : Rd d) :
    (1 + ‖(2 * π) • (c • ζ)‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      max 1 c * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (1 / 2 : ℝ) := by
  set a := ‖(2 * π) • ζ‖ ^ 2 with ha
  have ha0 : 0 ≤ a := sq_nonneg _
  have e : ‖(2 * π) • (c • ζ)‖ ^ 2 = c ^ 2 * a := by
    rw [smul_comm, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
  rw [e, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hm : 0 ≤ max 1 c := le_trans zero_le_one (le_max_left _ _)
  rw [← Real.sqrt_sq hm, ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have h1 : 1 ≤ max 1 c ^ 2 := by nlinarith [le_max_left (1 : ℝ) c]
  have h2 : c ^ 2 ≤ max 1 c ^ 2 := by
    have := le_max_right (1 : ℝ) c
    nlinarith
  nlinarith

/-- Auxiliary: `‖[φ(c·)]‖²_{H^{1/2}} ≤ c^{-d} max(1,c) ‖[φ]‖²_{H^{1/2}}` for a test `φ`, `c > 0`. -/
theorem norm_coord_dil_sq_le {φ : Rd d → ℝ} (hφ : IsTestFunction φ) {c : ℝ} (hc : 0 < c) :
    ‖coord (1 / 2) (fun x => φ (c • x))‖ ^ 2 ≤
      ((c ^ d)⁻¹ * max 1 c) * ‖coord (1 / 2) φ‖ ^ 2 := by
  have hψ := isTest_dil hφ hc.ne'
  have hF : ∀ ψ (hψ : IsTestFunction ψ), (⇑(𝓕 (H1Mathlib.testSchwartz hψ) : 𝓢(Rd d, ℂ)) : Rd d → ℂ) =
      𝓕 (fun x => (ψ x : ℂ)) := fun ψ hψ => by
    rw [SchwartzMap.fourier_coe]; rfl
  rw [norm_coord_sq _ hψ, norm_coord_sq _ hφ, hF _ hψ, hF _ hφ]
  set G : Rd d → ℝ := fun ξ =>
    (1 + ‖(2 * π) • ξ‖ ^ 2) ^ (1 / 2 : ℝ) * ‖𝓕 (fun x => (φ (c • x) : ℂ)) ξ‖ ^ 2 with hG
  have hsub := Measure.integral_comp_smul (μ := (volume : Measure (Rd d))) G c
  simp only [finrank_euclideanSpace_fin] at hsub
  have hcd : 0 < c ^ d := pow_pos hc d
  have hval : ∫ ξ, G ξ = c ^ d * ∫ ζ, G (c • ζ) := by
    rw [hsub, abs_of_pos (inv_pos.2 hcd), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hcd.ne',
      one_mul]
  have hGc : ∀ ζ, G (c • ζ) = (c ^ d)⁻¹ ^ 2 *
      ((1 + ‖(2 * π) • (c • ζ)‖ ^ 2) ^ (1 / 2 : ℝ) * ‖𝓕 (fun x => (φ x : ℂ)) ζ‖ ^ 2) := by
    intro ζ
    rw [hG]
    simp only
    rw [fourier_dil φ hc, inv_smul_smul₀ hc.ne',
      norm_smul ((c ^ d)⁻¹ : ℝ) (𝓕 (fun x => (φ x : ℂ)) ζ), Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hcd)]
    ring
  change ∫ ξ, G ξ ≤ _
  rw [hval]
  simp_rw [hGc]
  rw [integral_const_mul]
  have hint := (integrable_weighted (1 / 2) hφ).const_mul (max 1 c)
  rw [hF _ hφ] at hint
  have hmono : ∫ ζ, (1 + ‖(2 * π) • (c • ζ)‖ ^ 2) ^ (1 / 2 : ℝ) *
        ‖𝓕 (fun x => (φ x : ℂ)) ζ‖ ^ 2 ≤
      max 1 c * ∫ ζ, (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (1 / 2 : ℝ) * ‖𝓕 (fun x => (φ x : ℂ)) ζ‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun ζ => by positivity) hint
      (Eventually.of_forall fun ζ => ?_)
    dsimp only
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (weight_dil_le hc ζ) (sq_nonneg _)
  have hcd' : c ^ d * (c ^ d)⁻¹ ^ 2 = (c ^ d)⁻¹ := by
    field_simp
  calc c ^ d * ((c ^ d)⁻¹ ^ 2 * ∫ ζ, (1 + ‖(2 * π) • (c • ζ)‖ ^ 2) ^ (1 / 2 : ℝ) *
        ‖𝓕 (fun x => (φ x : ℂ)) ζ‖ ^ 2)
      = (c ^ d)⁻¹ * ∫ ζ, (1 + ‖(2 * π) • (c • ζ)‖ ^ 2) ^ (1 / 2 : ℝ) *
          ‖𝓕 (fun x => (φ x : ℂ)) ζ‖ ^ 2 := by rw [← mul_assoc, hcd']
    _ ≤ (c ^ d)⁻¹ * (max 1 c * ∫ ζ, (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (1 / 2 : ℝ) *
          ‖𝓕 (fun x => (φ x : ℂ)) ζ‖ ^ 2) := by gcongr
    _ = _ := by ring

/-- Auxiliary: the dilation `φ ↦ [φ(c·)]_{H^{1/2}}` on the test subspace. -/
def dilL {c : ℝ} (hc : c ≠ 0) : testSub d →ₗ[ℝ] Hhalf d where
  toFun φ := toHhalf fun x => (φ : Rd d → ℝ) (c • x)
  map_add' φ ψ := by
    have e : (fun x => ((φ + ψ : testSub d) : Rd d → ℝ) (c • x)) =
        (fun x => (φ : Rd d → ℝ) (c • x)) + fun x => (ψ : Rd d → ℝ) (c • x) := by
      funext x; simp
    rw [e, toHhalf_add (isTest_dil φ.2 hc) (isTest_dil ψ.2 hc)]
  map_smul' a φ := by
    have e : (fun x => ((a • φ : testSub d) : Rd d → ℝ) (c • x)) =
        a • fun x => (φ : Rd d → ℝ) (c • x) := by
      funext x; simp
    rw [e, toHhalf_smul a (isTest_dil φ.2 hc)]; rfl

/-- **The dilation on `H^{1/2}`**: for `c > 0` there is a bounded `D` with
`D [φ] = [φ(c·)]` on real tests (extension from the dense tests). -/
theorem exists_dil {c : ℝ} (hc : 0 < c) :
    ∃ D : Hhalf d →L[ℝ] Hhalf d, ∀ φ : Rd d → ℝ, IsTestFunction φ →
      D (toHhalf φ) = toHhalf fun x => φ (c • x) := by
  set K := √((c ^ d)⁻¹ * max 1 c) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hb : ∀ φ : testSub d, ‖dilL hc.ne' φ‖ ≤ K * ‖toHhalfL φ‖ := by
    intro φ
    change ‖toHhalf fun x => (φ : Rd d → ℝ) (c • x)‖ ≤ K * ‖toHhalf (φ : Rd d → ℝ)‖
    rw [norm_toHhalf _ (isTest_dil φ.2 hc.ne'), norm_toHhalf _ φ.2]
    have h := norm_coord_dil_sq_le φ.2 hc
    have hpos : 0 ≤ (c ^ d)⁻¹ * max 1 c := by
      have := le_max_left (1 : ℝ) c
      have : 0 < c ^ d := pow_pos hc d
      positivity
    have h2 : ‖coord (1 / 2) fun x => (φ : Rd d → ℝ) (c • x)‖ ^ 2 ≤
        (K * ‖coord (1 / 2) (φ : Rd d → ℝ)‖) ^ 2 := by
      rw [mul_pow, hK, Real.sq_sqrt hpos]; exact h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  refine ⟨(dilL hc.ne').extendOfNorm toHhalfL, fun φ hφ => ?_⟩
  exact LinearMap.extendOfNorm_eq denseRange_toHhalfL ⟨K, hb⟩ ⟨φ, hφ⟩

/-- **The cutoff multiplier by `η_R` on `H^{1/2}` at every radius `R > 0`**, from the one at
`R = 1` (A1's `UniformCutoffTarget` at `σ = 1/2`): `η_R φ = D_{1/R}(η · D_R φ)` with the
dilations `D_c φ = φ(c·)`. -/
theorem exists_cutoff_half (η : CutoffProfile d) {M : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)}
    (hM : IsCutoffMul (1 / 2) (1 / 2) (etaR η 1) M) {R : ℝ} (hR : 0 < R) :
    ∃ Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2), IsCutoffMul (1 / 2) (1 / 2) (etaR η R) Lη := by
  obtain ⟨D, hD⟩ := exists_dil (d := d) hR
  obtain ⟨D', hD'⟩ := exists_dil (d := d) (inv_pos.2 hR)
  set e : Hhalf d →L[ℝ] Hsob d (1 / 2) := hhalfEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  set e' : Hsob d (1 / 2) →L[ℝ] Hhalf d :=
    hhalfEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he' : ∀ φ, IsTestFunction φ → e' (toHsob (1 / 2) φ) = toHhalf φ := fun φ hφ => by
    change hhalfEquiv.symm _ = _
    rw [← hhalfEquiv_toHhalf hφ, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨e ∘L D' ∘L e' ∘L M ∘L e ∘L D ∘L e', fun φ hφ => ?_⟩
  have h1 := isTest_dil hφ hR.ne'
  have h2 := isTest_smooth_mul (PositiveRawMean.etaR_contDiff η 1) h1
  simp only [ContinuousLinearMap.comp_apply]
  rw [he' φ hφ, hD φ hφ]
  change hhalfEquiv (D' (e' (M (hhalfEquiv (toHhalf fun x => φ (R • x)))))) = _
  rw [hhalfEquiv_toHhalf h1, hM _ h1, he' _ h2, hD' _ h2, hhalfEquiv_toHhalf (isTest_dil h2
    (inv_pos.2 hR).ne')]
  congr 1
  funext x
  simp only [etaR, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, inv_one, one_mul]

/-- **B2 target, first theorem: `P:cameron-spatial-map`, `E` part without compactness**
(`integrated_cameron_mean.tex` lines 104-119, proof Step 1 lines 128-140, at revision edf7085f
(book 1.1.3)), at every radius `R > 0`, from the frozen outputs of A1 and A2. -/
theorem spatial_mean_map {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hA1 : ∀ η : CutoffProfile d, UniformCutoffTarget η) (hE : SobolevEmbedTarget d)
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s)
    (hH : HomogCovariance d alpha alpha0 Γ μ) (η : CutoffProfile d) :
    SpatialMeanMapTarget hH η := by
  intro R hR
  obtain ⟨M, hM, -⟩ := hA1 η (1 / 2) 1 le_rfl
  obtain ⟨Lη, hL⟩ := exists_cutoff_half η hM hR
  exact spatial_mean_map_at hE hA2 hH η hR hL

/-! ### Compactness of the map from compact row families -/

section CompactMap

variable {X H : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The span of finitely many vectors of a Hilbert basis. -/
def spanF {ι : Type*} (b : HilbertBasis ι ℝ H) (F : Finset ι) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range fun i : F => b i)

/-- The span of finitely many basis vectors is finite dimensional. -/
instance instFiniteDimensionalSpanF {ι : Type*} (b : HilbertBasis ι ℝ H) (F : Finset ι) :
    FiniteDimensional ℝ (spanF b F) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

omit [CompleteSpace H] in
/-- Auxiliary: the orthogonal projection is the best approximation from the subspace. -/
theorem norm_sub_starProjection_le {U : Submodule ℝ H} [U.HasOrthogonalProjection] (y : H)
    {x : H} (hx : x ∈ U) : ‖y - U.starProjection y‖ ≤ ‖y - x‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, by rintro _ ⟨_, rfl⟩; exact norm_nonneg _⟩ (⟨x, hx⟩ : U)

omit [CompleteSpace H] in
/-- Auxiliary: the finite-section projections converge to the identity uniformly on a compact
set (finite nets; TeX Step 4, "strong projection convergence is uniform on compact `𝓛` by a
finite-net argument", `integrated_cameron_mean.tex` lines 181-183 at revision edf7085f (book
1.1.3)). -/
theorem uniform_proj {ι : Type*} (b : HilbertBasis ι ℝ H) {𝒞 : Set H} (h𝒞 : IsCompact 𝒞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F₀ : Finset ι, ∀ F : Finset ι, F₀ ⊆ F → ∀ k ∈ 𝒞,
      ‖k - (spanF b F).starProjection k‖ < ε := by
  classical
  obtain ⟨t, ht𝒞, htf, hcov⟩ :=
    Metric.finite_approx_of_totallyBounded h𝒞.totallyBounded (ε / 2) (half_pos hε)
  have hy : ∀ y : H, ∃ G : Finset ι, ∀ F : Finset ι, G ⊆ F →
      ‖y - (spanF b F).starProjection y‖ < ε / 2 := by
    intro y
    obtain ⟨G, hG⟩ := Metric.tendsto_atTop.1 (b.hasSum_repr y) (ε / 2) (half_pos hε)
    refine ⟨G, fun F hF => ?_⟩
    have hmem : (∑ i ∈ F, b.repr y i • b i) ∈ spanF b F :=
      Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    calc ‖y - (spanF b F).starProjection y‖ ≤ ‖y - ∑ i ∈ F, b.repr y i • b i‖ :=
          norm_sub_starProjection_le y hmem
      _ < ε / 2 := by rw [← dist_eq_norm, dist_comm]; exact hG F hF
  choose G hG using hy
  refine ⟨htf.toFinset.biUnion G, fun F hF k hk => ?_⟩
  obtain ⟨y, hyt, hky⟩ := mem_iUnion₂.1 (hcov hk)
  have h1 := hG y F ((Finset.subset_biUnion_of_mem G (htf.mem_toFinset.2 hyt)).trans hF)
  set P := (spanF b F).starProjection
  have h2 : ‖(k - y) - P (k - y)‖ ≤ ‖k - y‖ := by
    simpa using norm_sub_starProjection_le (U := spanF b F) (k - y) (Submodule.zero_mem _)
  have h3 : ‖k - y‖ < ε / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hky
  calc ‖k - P k‖ = ‖((k - y) - P (k - y)) + (y - P y)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖(k - y) - P (k - y)‖ + ‖y - P y‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h2.trans_lt h3) h1
    _ = ε := by ring

/-- **The map `T` of a row with compact unit families is compact** (`P:cameron-spatial-map`,
Step 4, `integrated_cameron_mean.tex` lines 166-186 at revision edf7085f (book
1.1.3)): if `B z w ∈ 𝒞` for unit `z, w` with `𝒞` compact, then `T = rieszMap B` is the norm
limit of the finite-rank maps `T Q_F`, `Q_F` the projection onto finitely many basis vectors,
since `‖T(I - Q_F)‖ ≤ sup_{k ∈ 𝒞} ‖(I - Q_F) k‖ → 0`. -/
theorem isCompactOperator_rieszMap {B : X →L[ℝ] X →L[ℝ] H} {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ z w, ‖B z w‖ ≤ C * ‖z‖ * ‖w‖) {𝒞 : Set H} (h𝒞 : IsCompact 𝒞)
    (hmem : ∀ z w, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 → B z w ∈ 𝒞) : IsCompactOperator (rieszMap B hC hB) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ H
  set T := rieszMap B hC hB
  refine CompactOperatorFoundation.isCompactOperator_of_tendsto_finiteRank (l := atTop)
    (A := fun F : Finset w => T ∘L (spanF b F).starProjection) ?_ fun F => ?_
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨F₀, hF₀⟩ := uniform_proj b h𝒞 (half_pos hε)
    filter_upwards [eventually_ge_atTop F₀] with F hF
    rw [dist_eq_norm]
    set P := (spanF b F).starProjection
    have hbd : ‖T ∘L P - T‖ ≤ ε / 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q => ?_
      have e : (T ∘L P - T) q = -T (q - P q) := by
        simp [map_sub]
      rw [e, norm_neg]
      refine norm_rieszMap_apply_le B hC hB _ (by positivity) fun z w' => ?_
      have hpair : ∀ k : H, ⟪q - P q, k⟫ = ⟪q, k - P k⟫ := fun k => by
        rw [inner_sub_left, inner_sub_right, Submodule.inner_starProjection_left_eq_right]
      rw [hpair]
      rcases eq_or_ne z 0 with hz | hz
      · simp [hz]
      rcases eq_or_ne w' 0 with hw | hw
      · simp [hw]
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hw0 : 0 < ‖w'‖ := norm_pos_iff.2 hw
      set z₁ := ‖z‖⁻¹ • z
      set w₁ := ‖w'‖⁻¹ • w'
      have hz1 : ‖z₁‖ ≤ 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz0.ne']
      have hw1 : ‖w₁‖ ≤ 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0.ne']
      have hk : B z w' = (‖z‖ * ‖w'‖) • B z₁ w₁ := by
        simp only [z₁, w₁, map_smul, smul_apply, smul_smul]
        rw [show ‖z‖ * ‖w'‖ * (‖w'‖⁻¹ * ‖z‖⁻¹) = 1 by field_simp, one_smul]
      have hsm := hF₀ F hF _ (hmem z₁ w₁ hz1 hw1)
      rw [hk, map_smul P, ← smul_sub, inner_smul_right, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ * ‖w'‖)]
      calc ‖z‖ * ‖w'‖ * |⟪q, B z₁ w₁ - P (B z₁ w₁)⟫| ≤
            ‖z‖ * ‖w'‖ * (‖q‖ * ‖B z₁ w₁ - P (B z₁ w₁)‖) := by
            gcongr; exact abs_real_inner_le_norm _ _
        _ ≤ ‖z‖ * ‖w'‖ * (‖q‖ * (ε / 2)) := by gcongr
        _ = ε / 2 * ‖q‖ * ‖z‖ * ‖w'‖ := by ring
    linarith
  · refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.map (T : H →ₗ[ℝ] (X →L[ℝ] X)) (spanF b F)) ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨(spanF b F).starProjection q, Submodule.starProjection_apply_mem _ q, rfl⟩

end CompactMap

/-! ### `P:cameron-spatial-map`, `E` part, with compactness -/

/-- Auxiliary: `η_R` is a real test function (`R > 0`). -/
theorem etaR_isTest (η : CutoffProfile d) {R : ℝ} (hR : 0 < R) : IsTestFunction (etaR η R) := by
  refine ⟨PositiveRawMean.etaR_contDiff η R, ?_⟩
  have h : HasCompactSupport η.η :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 2)
      ((subset_tsupport _).trans η.support_subset)
  exact h.comp_smul (inv_ne_zero hR.ne')

/-- **Compact localized factors** (`integrated_cameron_mean.tex` Step 2, lines 148-150 at
revision edf7085f (book 1.1.3)): multiplication by `η_R` followed by `H^{1/2} ↪ H^s`,
`s < 1/2`, is compact, by `P:cutoff-singular-values` with gain `1/2 - s` (`CutoffCompact`). -/
theorem isCompactOperator_embed_cutoff (hc : CutoffCompact d) {η : CutoffProfile d} {R s : ℝ}
    (hR : 0 < R) (hs : s < 1 / 2) {ι : Hsob d (1 / 2) →L[ℝ] Hsob d s}
    {Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)} (hι : IsSobolevEmbed (1 / 2) s ι)
    (hL : IsCutoffMul (1 / 2) (1 / 2) (etaR η R) Lη) : IsCompactOperator (ι ∘L Lη) := by
  have h := hc.compact (etaR η R) s (1 / 2 - s) (etaR_isTest η hR) (by linarith)
  unfold CutoffCompactTarget at h
  rw [show s + (1 / 2 - s) = (1 / 2 : ℝ) by ring] at h
  obtain ⟨⟨K, hK, hKc⟩, huniq⟩ := h
  have hmul : IsCutoffMul (1 / 2) s (etaR η R) (ι ∘L Lη) := fun φ hφ => by
    rw [ContinuousLinearMap.comp_apply, hL φ hφ,
      hι _ (isTest_smooth_mul (PositiveRawMean.etaR_contDiff η R) hφ)]
  rw [huniq _ _ hmul hK]
  exact hKc

/-- Auxiliary: `T q = (ι η_R Λ⁻¹)† ∘ G_q` with `⟪G_q z, y⟫ = ⟪q, P(ι η_R z₁, y)⟫`; so the values
of `meanMap` are compact when the right factor is (TeX Step 3, lines 152-163). -/
theorem isCompactOperator_meanMap_apply {s A : ℝ} {P : Hsob d s →L[ℝ] Hsob d s →L[ℝ] Hsp S}
    (hPA : ∀ u v, ‖P u v‖ ≤ A * ‖u‖ * ‖v‖) (hA : 0 ≤ A) (ι : Hsob d (1 / 2) →L[ℝ] Hsob d s)
    (Lη : Hsob d (1 / 2) →L[ℝ] Hsob d (1 / 2)) (hK : IsCompactOperator (rightL ι Lη))
    (q : Hsp S) : IsCompactOperator (meanMap S P hPA hA ι Lη q) := by
  set B' : E d →L[ℝ] Hsob d s →L[ℝ] Hsp S := P ∘L leftL ι Lη
  have hB' : ∀ z y, ‖B' z y‖ ≤ (A * ‖leftL ι Lη‖) * ‖z‖ * ‖y‖ := fun z y => by
    change ‖P (leftL ι Lη z) y‖ ≤ _
    calc ‖P (leftL ι Lη z) y‖ ≤ A * ‖leftL ι Lη z‖ * ‖y‖ := hPA _ _
      _ ≤ A * (‖leftL ι Lη‖ * ‖z‖) * ‖y‖ := by gcongr; exact (leftL ι Lη).le_opNorm z
      _ = _ := by ring
  set G := rieszMap B' (by positivity) hB' q
  have heq : meanMap S P hPA hA ι Lη q = ContinuousLinearMap.adjoint (rightL ι Lη) ∘L G := by
    ext1 z
    refine ext_inner_right ℝ fun w => ?_
    rw [inner_meanMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      inner_rieszMap]
    rfl
  rw [heq]
  exact (CompactOperatorFoundation.isCompactOperator_adjoint _ hK).comp_clm G

/-- **B2 target, second theorem: `P:cameron-spatial-map`, `E` part** (`integrated_cameron_mean.tex`
lines 104-119, proof 121-186, at revision edf7085f (book 1.1.3)), at every radius
`R > 0`: a `CameronSpatialMap` (compact map, compact values, smooth-test formula, test-state
row) whose row holds at all states for every `α/4 < s < 1/2`; from the frozen outputs of A1,
A2 and the compactness sentence of `P:cutoff-singular-values` (`CutoffCompact`, item B1). -/
theorem cameron_spatial_map {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hA1 : ∀ η : CutoffProfile d, UniformCutoffTarget η) (hE : SobolevEmbedTarget d)
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s)
    (hH : HomogCovariance d alpha alpha0 Γ μ) (η : CutoffProfile d) (hc : CutoffCompact d) :
    CameronSpatialTarget hH η := by
  intro R hR
  obtain ⟨hs1, hs2⟩ := s0_mem hH
  obtain ⟨Cs, hCs0, hCs⟩ := hA2 _ hs1 hs2
  obtain ⟨P, hP, -, hPA, -⟩ := hCs alpha0 Γ μ hH
  obtain ⟨ι, hι, -⟩ := hE (1 / 2) ((alpha / 4 + 1 / 2) / 2) hs2.le
  obtain ⟨M, hM, -⟩ := hA1 η (1 / 2) 1 le_rfl
  obtain ⟨Lη, hL⟩ := exists_cutoff_half η hM hR
  have hA : 0 ≤ Cs ^ 2 * √(SpatialFourLinear.Rsp Γ alpha) := by positivity
  have hsm := isSpatialMeanMap_meanMap (S := SpData.ofHomog hH) hR hPA hA hP hι hL
  have hK := isCompactOperator_embed_cutoff hc hR hs2 hι hL
  have hK1 : IsCompactOperator (leftL ι Lη) :=
    hK.comp_clm (hhalfEquiv.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      ContinuousLinearMap.fst ℝ (Hhalf d) (Hmhalf d) ∘L (eEquiv (d := d)).toContinuousLinearMap)
  have hK2 : IsCompactOperator (rightL ι Lη) :=
    hK.comp_clm (hhalfEquiv.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (lam (d := d)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      ContinuousLinearMap.snd ℝ (Hhalf d) (Hmhalf d) ∘L (eEquiv (d := d)).toContinuousLinearMap)
  set 𝒞 : Set (Hsp (SpData.ofHomog hH)) := (fun p => P p.1 p.2) ''
    (closure (leftL ι Lη '' Metric.closedBall 0 1) ×ˢ
      closure (rightL ι Lη '' Metric.closedBall 0 1))
  have h𝒞 : IsCompact 𝒞 :=
    ((hK1.isCompact_closure_image_closedBall 1).prod
      (hK2.isCompact_closure_image_closedBall 1)).image P.continuous₂
  have hmem : ∀ z w, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 → kRowL (SpData.ofHomog hH) P ι Lη z w ∈ 𝒞 :=
    fun z w hz hw => ⟨(leftL ι Lη z, rightL ι Lη w),
      ⟨subset_closure ⟨z, mem_closedBall_zero_iff.2 hz, rfl⟩,
        subset_closure ⟨w, mem_closedBall_zero_iff.2 hw, rfl⟩⟩, rfl⟩
  exact ⟨⟨meanMap _ P hPA hA ι Lη, isCompactOperator_rieszMap _ _ h𝒞 hmem,
    isCompactOperator_meanMap_apply hPA hA ι Lη hK2, hsm.1, hsm.2⟩,
    fun s _ _ => spatialRowAll_meanMap hPA hA hP hι hL s⟩

end StratonovichHAMSecondMoment.CameronSpatial
