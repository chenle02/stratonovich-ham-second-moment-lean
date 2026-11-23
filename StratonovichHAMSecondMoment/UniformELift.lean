module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L15, item L15-UM, UM-1 (agent A; scope (a), approved by Le on 2026-11-19):
`L:uniform-E-lift` in the operator form frozen by the interface
`StratonovichHAMSecondMoment.UniformMeanInterface` (commit 06c3c6a).

TeX anchors (revision 0788ddee, book 1.1.0, read with `git show 0788ddee:notes/...`; the same
line numbers at edf7085f, book 1.1.3):
`notes/integrated_uniform_products.tex` lines 29-31 (`V_q = m_R(Γ*q)`, `M_q`, `L_q^E`,
`𝒱_{E,R}`), lines 33-46 (statement of `L:uniform-E-lift`, `E:uniform-E-pairing` lines 39-41) and
lines 48-57 (proof: the zero columns persist, `M_n → M` with the norm equality; `χ_R = 1` near
`supp m_R`, `V = M χ_R` with its support; `M u = V u` on tests; uniqueness; symmetry and the
pairing bound pass to the limit).  `notes/integrated_uniform_mean.tex` lines 7-10 (the cutoff
profile `η`, `m_R = η(·/R)²`).

Main results:
* `uniform_E_lift S η : UniformELiftTarget S η`: for `R ≥ 1` every `L ∈ 𝒱_{E,R}` is `B_E(M)`
  with `‖L‖ = ‖M‖` and a unique `V ∈ H^{-1/2}` supported in `supp m_R` with `M u = V u` on tests;
* `uniform_E_pairing S η : UniformEPairingTarget S η`: the pairing `⟨M u, w⟩` is symmetric and
  bounded by `‖L‖ ‖u‖ ‖w‖` (`E:uniform-E-pairing`);
* `uniform_E_lift_paper`: both, for the covariance data of the paper (`SpData.ofHomog hH`).
Both are unconditional (no named input); every covariance and every cutoff profile.

Lean proof route (as the TeX's): `B_E` is an isometry from the complete space
`𝓛(H^{1/2}, H^{-1/2})`, so `𝒱_{E,R} = B_E(closure G)` with `G` the multipliers `M_q`
(`norm_BE`, `isometry_BE` of UM-0).  With a fixed test `χ_R` equal to `1` on the ball of radius
`3R` (which contains `supp m_R ⊆ B̄(0, 2R)`), the potential is `V = M χ_R`; the three properties
"`M u = (Mχ_R) u` on tests", "`Mχ_R` vanishes on tests supported off `supp m_R`" and "the
pairing is symmetric" hold for each `M_q` (by `dpair_toHmhalf_toHhalf`, they are identities of
the integrals `∫ V_q u φ`), are closed in `M`, hence hold on the closure.  Uniqueness: two
potentials agree on `χ_R φ` (by `ActsAs`) and on `(1-χ_R) φ` (by the support condition), so on
all tests, hence everywhere by density (`denseRange_toHhalf`).

TeX presentation issue (reported to the manuscript owner, recorded in `docs/l15/INTERFACE.md`
section 6.1, and repaired in the manuscript): at revision c3c2431d (book v1.0.2) the statement of
`L:uniform-E-lift` did not state how `V` is tied to `L`.  At revision edf7085f (book 1.1.3) it
does (lines 35-38: `M u = V u` as distributions for every test `u`), which is the relation
`ActsAs V M` of the frozen target and of the proof (lines 55-57).

No `sorry`, no axiom; every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.UniformMeanFoundation

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace

namespace StratonovichHAMSecondMoment.UniformMeanInterface

open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (IsTestFunction)
open OccupationCompletion (SpData)
open VariationalDilation (conv)

variable {d : ℕ}

/-! ### The support of `m_R` and the cutoff `χ_R` -/

/-- Auxiliary: `supp m_R ⊆ B̄(0, 2R)` (`η` is supported in the closed radius-two ball,
`integrated_uniform_mean.tex` lines 7-9 at revision edf7085f (book 1.1.3)). -/
theorem tsupport_mR_subset (η : CutoffProfile d) {R : ℝ} (hR : 0 < R) :
    tsupport (mR η R) ⊆ Metric.closedBall 0 (2 * R) := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  have h1 : η.η (R⁻¹ • x) ≠ 0 := fun h => hx (by simp [mR, mRfun, h])
  have h2 : R⁻¹ • x ∈ Metric.closedBall (0 : Rd d) 2 :=
    η.support_subset (subset_tsupport _ h1)
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)] at h2
  rw [Metric.mem_closedBall, dist_zero_right]
  have := (inv_mul_le_iff₀ hR).mp h2
  linarith

/-- The cutoff `χ_R`: a smooth bump equal to `1` on `B̄(0, 3R)` (so near `supp m_R`) and
supported in `B̄(0, 4R)` (the TeX's "real compact smooth `χ_R = 1` near `supp m_R`",
`integrated_uniform_products.tex` line 52 at revision edf7085f (book 1.1.3)). -/
def chiBump {R : ℝ} (hR : 0 < R) : ContDiffBump (0 : Rd d) :=
  ⟨3 * R, 4 * R, by positivity, by linarith⟩

/-- Auxiliary: `χ_R` is a test function. -/
theorem chiBump_isTest {R : ℝ} (hR : 0 < R) : IsTestFunction (chiBump (d := d) hR : Rd d → ℝ) :=
  ⟨(chiBump hR).contDiff, (chiBump hR).hasCompactSupport⟩

/-- Auxiliary: `χ_R = 1` on the open ball of radius `3R`. -/
theorem chiBump_eq_one {R : ℝ} (hR : 0 < R) {x : Rd d} (hx : ‖x‖ < 3 * R) :
    (chiBump hR : Rd d → ℝ) x = 1 :=
  (chiBump hR).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hx.le)

/-- Auxiliary: `χ_R = 1` on `supp m_R`. -/
theorem chiBump_eq_one_of_mR {η : CutoffProfile d} {R : ℝ} (hR : 0 < R) {x : Rd d}
    (hx : mR η R x ≠ 0) : (chiBump hR : Rd d → ℝ) x = 1 := by
  have h := tsupport_mR_subset η hR (subset_tsupport _ hx)
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact chiBump_eq_one hR (by linarith)

/-- Auxiliary: `(1 - χ_R) φ` is a test supported off `supp m_R`. -/
theorem one_sub_chi_mul {η : CutoffProfile d} {R : ℝ} (hR : 0 < R) {φ : Rd d → ℝ}
    (hφ : IsTestFunction φ) :
    IsTestFunction (fun x => (1 - (chiBump hR : Rd d → ℝ) x) * φ x) ∧
      Disjoint (tsupport fun x => (1 - (chiBump hR : Rd d → ℝ) x) * φ x)
        (tsupport (mR η R)) := by
  refine ⟨⟨(contDiff_const.sub (chiBump hR).contDiff).mul hφ.1, hφ.2.mul_left⟩, ?_⟩
  have hs : tsupport (fun x => (1 - (chiBump hR : Rd d → ℝ) x) * φ x) ⊆
      (Metric.ball (0 : Rd d) (3 * R))ᶜ := by
    refine closure_minimal (fun x hx => ?_) Metric.isOpen_ball.isClosed_compl
    intro hb
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact hx (by simp [chiBump_eq_one hR hb])
  refine Disjoint.mono_left hs (Set.disjoint_compl_left_iff_subset.mpr fun x hx => ?_)
  have h := tsupport_mR_subset η hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at h
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-! ### The duality pairing -/

/-- Auxiliary: `(v, u) ↦ ⟨v, u⟩_{H^{-1/2},H^{1/2}}` is continuous. -/
theorem continuous_dpair : Continuous fun p : Hmhalf d × Hhalf d => dpair p.1 p.2 :=
  continuous_inner.comp ((lam (d := d)).symm.continuous.comp continuous_fst |>.prodMk
    continuous_snd)

/-- Auxiliary: the duality is additive in the `H^{1/2}` argument. -/
theorem dpair_add_right (v : Hmhalf d) (u u' : Hhalf d) :
    dpair v (u + u') = dpair v u + dpair v u' := inner_add_right _ _ _

/-- Auxiliary: `|⟨v, u⟩| ≤ ‖v‖ ‖u‖`. -/
theorem abs_dpair_le (v : Hmhalf d) (u : Hhalf d) : |dpair v u| ≤ ‖v‖ * ‖u‖ := by
  rw [dpair, ← LinearIsometryEquiv.norm_map lam.symm v]
  exact abs_real_inner_le_norm _ _

/-- Auxiliary: an element of `H^{-1/2}` is determined by its duality with `H^{1/2}`. -/
theorem eq_of_dpair_eq {v v' : Hmhalf d} (h : ∀ u : Hhalf d, dpair v u = dpair v' u) :
    v = v' :=
  lam.symm.injective (ext_inner_right ℝ h)

/-- Auxiliary: an element of `H^{-1/2}` is determined by its duality with real tests
(density of tests in `H^{1/2}`). -/
theorem eq_of_dpair_test_eq {v v' : Hmhalf d}
    (h : ∀ φ : Rd d → ℝ, IsTestFunction φ → dpair v (toHhalf φ) = dpair v' (toHhalf φ)) :
    v = v' := by
  refine eq_of_dpair_eq fun u => ?_
  have hc : ∀ w : Hmhalf d, Continuous fun x : Hhalf d => dpair w x := fun w =>
    continuous_dpair.comp (continuous_const.prodMk continuous_id)
  have := Continuous.ext_on denseRange_toHhalf (hc v) (hc v') (by
    rintro x ⟨φ, hφ, rfl⟩; exact h φ hφ)
  exact congrFun this u

/-! ### The generators `M_q` and the closure -/

/-- The multipliers `M_q` by `V_q = m_R (Γ * q)`, `q` a real test
(`integrated_uniform_products.tex` lines 29-30 at revision edf7085f (book 1.1.3)). -/
def genSet (S : SpData d) (η : CutoffProfile d) (R : ℝ) : Set (Hhalf d →L[ℝ] Hmhalf d) :=
  {M | ∃ q : Rd d → ℝ, IsTestFunction q ∧ IsMultiplier (fun x => mR η R x * conv S.Γ q x) M}

/-- **`𝒱_{E,R} = B_E(closure G)`**: the zero columns persist and the limits are `B_E` of limits
of multipliers (`integrated_uniform_products.tex` lines 49-51 at revision edf7085f
(book 1.1.3)); `B_E` is an isometry from a complete space. -/
theorem VER_eq (S : SpData d) (η : CutoffProfile d) (R : ℝ) :
    VER S η R = BE '' closure (genSet S η R) := by
  have hset : {L : E d →L[ℝ] E d | ∃ (q : Rd d → ℝ) (M : Hhalf d →L[ℝ] Hmhalf d),
      IsTestFunction q ∧ IsMultiplier (fun x => mR η R x * conv S.Γ q x) M ∧ L = BE M} =
      BE '' genSet S η R := by
    ext L
    constructor
    · rintro ⟨q, M, hq, hM, rfl⟩
      exact ⟨M, ⟨q, hq, hM⟩, rfl⟩
    · rintro ⟨M, ⟨q, hq, hM⟩, rfl⟩
      exact ⟨q, M, hq, hM, rfl⟩
  rw [VER, hset, isometry_BE.isClosedEmbedding.closure_image_eq]

/-- Auxiliary: a generator's potential `V_q` vanishes off `supp m_R`. -/
theorem gen_zero {S : SpData d} {η : CutoffProfile d} {R : ℝ} {q : Rd d → ℝ} {x : Rd d}
    (hx : mR η R x = 0) : mR η R x * conv S.Γ q x = 0 := by
  rw [hx, zero_mul]

/-- Auxiliary: the pairing of a generator on tests, `⟨M_q u, w⟩ = ∫ V_q u w`. -/
theorem gen_pair {V : Rd d → ℝ} {M : Hhalf d →L[ℝ] Hmhalf d} (hM : IsMultiplier V M)
    {u w : Rd d → ℝ} (hu : IsTestFunction u) (hw : IsTestFunction w) :
    dpair (M (toHhalf u)) (toHhalf w) = ∫ x, V x * u x * w x := by
  rw [hM.2 u hu, dpair_toHmhalf_toHhalf (isTest_smooth_mul hM.1 hu) hw]

/-- The three closed properties of `M` used for `L:uniform-E-lift`, with the potential
`V = M χ_R`: `M u = V u` on tests (lines 55-56), `V` vanishes on tests supported off `supp m_R`
(line 54), and the pairing `⟨M u, w⟩` is symmetric (line 57) (`integrated_uniform_products.tex`
at revision edf7085f (book 1.1.3)). -/
def LiftProps (η : CutoffProfile d) {R : ℝ} (hR : 0 < R) (M : Hhalf d →L[ℝ] Hmhalf d) : Prop :=
  (∀ u φ : Rd d → ℝ, IsTestFunction u → IsTestFunction φ →
      dpair (M (toHhalf u)) (toHhalf φ) =
        dpair (M (toHhalf (chiBump hR : Rd d → ℝ))) (toHhalf fun x => u x * φ x)) ∧
    (∀ φ : Rd d → ℝ, IsTestFunction φ → Disjoint (tsupport φ) (tsupport (mR η R)) →
      dpair (M (toHhalf (chiBump hR : Rd d → ℝ))) (toHhalf φ) = 0) ∧
    ∀ u w : Hhalf d, dpair (M u) w = dpair (M w) u

/-- Auxiliary: `M ↦ ⟨M x, y⟩` is continuous. -/
theorem continuous_dpair_apply (x y : Hhalf d) :
    Continuous fun M : Hhalf d →L[ℝ] Hmhalf d => dpair (M x) y :=
  continuous_dpair.comp ((continuous_eval_const x).prodMk continuous_const)

/-- Auxiliary: the set of `M` with `LiftProps` is closed. -/
theorem isClosed_liftProps (η : CutoffProfile d) {R : ℝ} (hR : 0 < R) :
    IsClosed {M : Hhalf d →L[ℝ] Hmhalf d | LiftProps η hR M} := by
  simp only [LiftProps, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun u => isClosed_iInter fun φ => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => isClosed_eq (continuous_dpair_apply _ _)
      (continuous_dpair_apply _ _)).inter ((isClosed_iInter fun φ => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => isClosed_eq (continuous_dpair_apply _ _) continuous_const).inter
      (isClosed_iInter fun u => isClosed_iInter fun w =>
        isClosed_eq (continuous_dpair_apply _ _) (continuous_dpair_apply _ _)))

/-- Auxiliary: a symmetric pairing on tests is symmetric on `H^{1/2}` (density). -/
theorem dpair_symm_of_test {M : Hhalf d →L[ℝ] Hmhalf d}
    (h : ∀ u w : Rd d → ℝ, IsTestFunction u → IsTestFunction w →
      dpair (M (toHhalf u)) (toHhalf w) = dpair (M (toHhalf w)) (toHhalf u))
    (u w : Hhalf d) : dpair (M u) w = dpair (M w) u := by
  have hcl : ∀ y : Hhalf d, Continuous fun x : Hhalf d => dpair (M x) y := fun y =>
    continuous_dpair.comp ((M.continuous).prodMk continuous_const)
  have hcr : ∀ y : Hhalf d, Continuous fun x : Hhalf d => dpair (M y) x := fun y =>
    continuous_dpair.comp (continuous_const.prodMk continuous_id)
  -- first `w` a test, `u` arbitrary
  have step1 : ∀ ψ : Rd d → ℝ, IsTestFunction ψ → ∀ x : Hhalf d,
      dpair (M x) (toHhalf ψ) = dpair (M (toHhalf ψ)) x := by
    intro ψ hψ
    have := Continuous.ext_on denseRange_toHhalf (hcl (toHhalf ψ)) (hcr (toHhalf ψ)) (by
      rintro x ⟨φ, hφ, rfl⟩; exact h φ ψ hφ hψ)
    exact congrFun this
  have := Continuous.ext_on denseRange_toHhalf (hcr u) (hcl u) (by
    rintro x ⟨ψ, hψ, rfl⟩; exact step1 ψ hψ u)
  exact congrFun this w

/-- Auxiliary: every generator `M_q` has `LiftProps` (`integrated_uniform_products.tex`
lines 52-57 at revision edf7085f (book 1.1.3), for `M_n = M_q`). -/
theorem liftProps_gen {S : SpData d} {η : CutoffProfile d} {R : ℝ} (hR : 0 < R)
    {M : Hhalf d →L[ℝ] Hmhalf d} (hM : M ∈ genSet S η R) : LiftProps η hR M := by
  obtain ⟨q, -, hV⟩ := hM
  have hχ := chiBump_isTest (d := d) hR
  refine ⟨fun u φ hu hφ => ?_, fun φ hφ hdisj => ?_, dpair_symm_of_test fun u w hu hw => ?_⟩
  · rw [gen_pair hV hu hφ, gen_pair hV hχ (isTest_mul hu hφ)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : mR η R x = 0
    · simp [hx]
    · simp only [chiBump_eq_one_of_mR hR hx]; ring
  · rw [gen_pair hV hχ hφ]
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
    by_cases hx : φ x = 0
    · simp [hx]
    · have hxm : mR η R x = 0 := by
        by_contra hne
        exact Set.disjoint_left.mp hdisj (subset_tsupport _ hx) (subset_tsupport _ hne)
      simp [hxm]
  · rw [gen_pair hV hu hw, gen_pair hV hw hu]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring

/-- Auxiliary: every `M` in the closure of the generators has `LiftProps`
(the properties pass to the limit, `integrated_uniform_products.tex` lines 52-57 at revision
edf7085f (book 1.1.3)). -/
theorem liftProps_closure {S : SpData d} {η : CutoffProfile d} {R : ℝ} (hR : 0 < R)
    {M : Hhalf d →L[ℝ] Hmhalf d} (hM : M ∈ closure (genSet S η R)) : LiftProps η hR M :=
  closure_minimal (fun _ h => liftProps_gen hR h) (isClosed_liftProps η hR) hM

/-! ### Uniqueness of the potential -/

/-- **Uniqueness of the potential** (`integrated_uniform_products.tex` line 57 at revision
edf7085f (book 1.1.3)): two `V, V' ∈ H^{-1/2}` supported in `supp m_R` with `M u = V u` and
`M u = V' u` on tests coincide. -/
theorem potential_unique {η : CutoffProfile d} {R : ℝ} (hR : 0 < R)
    {M : Hhalf d →L[ℝ] Hmhalf d} {V V' : Hmhalf d}
    (hS : SupportedIn V (tsupport (mR η R))) (hA : ActsAs V M)
    (hS' : SupportedIn V' (tsupport (mR η R))) (hA' : ActsAs V' M) : V' = V := by
  refine eq_of_dpair_test_eq fun φ hφ => ?_
  have hχ := chiBump_isTest (d := d) hR
  obtain ⟨h1, hdisj⟩ := one_sub_chi_mul (η := η) hR hφ
  have hsplit : φ = (fun x => (chiBump hR : Rd d → ℝ) x * φ x) +
      fun x => (1 - (chiBump hR : Rd d → ℝ) x) * φ x := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hsplit, toHhalf_add (isTest_mul hχ hφ) h1, dpair_add_right, dpair_add_right,
    hS' _ h1 hdisj, hS _ h1 hdisj, ← hA' _ _ hχ hφ, ← hA _ _ hχ hφ]

/-! ### The UM-1 targets -/

/-- **`L:uniform-E-lift`, operator form** (UM-1; `integrated_uniform_products.tex` lines 33-38,
proof lines 48-57, at revision edf7085f (book 1.1.3)): for every covariance, every cutoff
profile and `R ≥ 1`, each `L ∈ 𝒱_{E,R}` is `B_E(M)` with `‖L‖ = ‖M‖`, and there is a unique
`V ∈ H^{-1/2}` supported in `supp m_R` with `M u = V u` on tests (namely `V = M χ_R`). -/
theorem uniform_E_lift (S : SpData d) (η : CutoffProfile d) : UniformELiftTarget S η := by
  intro R hR L hL
  have hR0 : (0 : ℝ) < R := by linarith
  rw [VER_eq] at hL
  obtain ⟨M, hM, rfl⟩ := hL
  obtain ⟨hA, hS, -⟩ := liftProps_closure hR0 hM
  refine ⟨M, rfl, norm_BE M, M (toHhalf (chiBump hR0 : Rd d → ℝ)), ⟨hS, hA⟩, ?_⟩
  rintro V' ⟨hS', hA'⟩
  exact potential_unique hR0 hS hA hS' hA'

/-- **`E:uniform-E-pairing` and the symmetry of the pairing** (UM-1;
`integrated_uniform_products.tex` lines 38-41 and 44-45, proof line 57, at revision edf7085f
(book 1.1.3)): for `R ≥ 1` and `L = B_E(M) ∈ 𝒱_{E,R}`, `⟨M u, w⟩ = ⟨M w, u⟩` and
`|⟨M u, w⟩| ≤ ‖L‖ ‖u‖ ‖w‖` for all real `u, w ∈ H^{1/2}`. -/
theorem uniform_E_pairing (S : SpData d) (η : CutoffProfile d) : UniformEPairingTarget S η := by
  intro R hR L hL M hLM
  have hR0 : (0 : ℝ) < R := by linarith
  rw [VER_eq] at hL
  obtain ⟨M', hM', rfl⟩ := hL
  obtain rfl := BE_injective hLM
  obtain ⟨-, -, hsymm⟩ := liftProps_closure hR0 hM'
  refine ⟨hsymm, fun u w => ?_⟩
  rw [vPair, norm_BE]
  calc |dpair (M' u) w| ≤ ‖M' u‖ * ‖w‖ := abs_dpair_le _ _
    _ ≤ ‖M'‖ * ‖u‖ * ‖w‖ := mul_le_mul_of_nonneg_right (M'.le_opNorm u) (norm_nonneg _)

/-- **`L:uniform-E-lift` for the paper's covariance data** (UM-1 wrapper;
`integrated_uniform_products.tex` lines 33-46 at revision edf7085f (book 1.1.3)). -/
theorem uniform_E_lift_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (η : CutoffProfile d) :
    UniformELiftTarget (SpData.ofHomog hH) η ∧ UniformEPairingTarget (SpData.ofHomog hH) η :=
  ⟨uniform_E_lift _ η, uniform_E_pairing _ η⟩

end StratonovichHAMSecondMoment.UniformMeanInterface
