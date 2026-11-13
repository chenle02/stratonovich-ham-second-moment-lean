module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:spatial-static-controls` (Smooth temporal controls) of
`notes/integrated_spatial_occupation.tex` at revision a284420: statement TeX
lines 40-54 (the definition of `λ_z(c)²`, lines 42-46; display
`E:spatial-static-score`, lines 50-53), proof lines 56-96.  Standing
assumptions of the section (lines 4-10): a nonzero original covariance from
`H:homog`, `a = α₀`; for smooth compact `z`, `U_z = Γ * z` pointwise (lines
37-38).  The wrappers carry `HomogHypothesis.HomogCovariance d α α₀ Γ μ`,
`Γ ≠ 0` and use the exponent `α₀`.

Definitions reused: `VariationalDilation.conv` (`(Γ * φ)(x) = ∫ φ(x-y) Γ(dy)`),
`mean`, `rawCost` (the integral form of `v_Ψ`), `rate`, `integratedRate` and
`CPos` (`E:variational-positive-class`); `WeakSobolev.rayleighSet` (the real
Rayleigh values over unit `H^1` pairs); `TemporalEquilibrium.density`
(`f_a`) and `mass` (`M_a`, `E:temporal-equilibrium-mass`);
`OccupationKernelRow.pairing` (`B_Γ` of `E:spatial-physical-pair`, an extended
nonnegative integral).  New definitions: `lamSq U c`
(`= sup{c ∫ U g² - ‖∇g‖₂²}`), `lam U c = √(lamSq U c)`, `lamZ Γ z = lam (Γ * z)`
(`λ_z`), the cutoff `cut n` and `fn a n = f_a · cut n` (`f_n`), `ctrl a n z =
f_n ⊗ z` (`Ψ_n`), `kn a n` (`k_n`), `zE z = ofReal ∘ z`, and the named input
`RayleighFloor` (discharged in `SpatialOccupationCompleted`).  The score set,
`S1Bdd` and `S1pos` are those of `VariationalRate` (`score1Set`, `S1Bdd`,
`S1pos`); the weak gradient of a test function is
`VariationalFloor.hasWeakGradient_of_test`.  `pairing_eq_spatialPair` bridges
`OccupationKernelRow.pairing` to the real pairing
`SpatialFourierBound.spatialPair`, and `isUnitH1_of_unitTest` connects
`SpatialFourierBound.IsUnitTest` to `IsUnitH1`.

Formalized:
* `spatial_static_controls_rate_paper` (part (i)): for nonnegative nonzero
  `z ∈ C_c^∞`, `U_z(x)` is a genuine integral; for `c > 0` the Rayleigh set of
  `c U_z` is nonempty and bounded above, `λ_z(c)² > 0`, `λ_z(c) > 0`; `λ_z` is
  Lipschitz on every `[c₁, c₂]`, `c₁ > 0`.  General form `static_rate`, which
  also gives the global bound `|λ_z(c)² - λ_z(c')²| ≤ M |c - c'|` for every
  upper bound `M` of `U_z` (the TeX's constant `‖U_z‖_∞`, lines 62-63), without the
  floor.
* `spatial_static_score_paper` (part (ii), `E:spatial-static-score` in the
  existential form of Le's decision 2): `B_Γ(z,z) < ∞`, and every
  `y < λ_z(1) - (M_a/2) B_Γ(z,z)` is exceeded by `I_Ψ - v_Ψ/2` for some
  `Ψ ∈ C_pos` with integrable rate and cost integrands.  General form
  `static_score`; the convergence `I_{Ψ_n} - v_{Ψ_n}/2 → λ_z(1) - (M_a/2)B_Γ(z,z)`
  is `score_tendsto`, and `ctrl_genuine` shows every value involved is a
  genuine integral or supremum.
* `spatial_static_score_sSup_paper`: the sSup form `S_1^pos ≥ λ_z(1) -
  (M_a/2) B_Γ(z,z)` on the named input `S1Bdd`.
* `pairing_bridge`: `B_Γ(z,z) = ofReal (∫ z U_z)`, finite, with real value
  `∫ z U_z ≥ 0` (TeX line 88: "the spatial factor is finite").

Supplied inputs (named hypotheses):
* `RayleighFloor Γ` (part (i) only, for positivity): for every nonnegative
  nonzero test function `z`, the Rayleigh set of `Γ * z` contains a positive
  value.  It stands for the dilation floor lemma of wave item L6-d ("for
  `V ≥ Γ * z`, `z ≥ 0` nonzero compactly supported, `Γ ≠ 0`, `α < 2`, the
  Rayleigh supremum of `V` over unit `H^1` tests is positive") at `V = Γ * z`,
  so it is no stronger than that lemma; the integrator instantiates it.  Note
  that, given the boundedness of `U_z` proved here, it is equivalent to the
  positivity of `λ_z(1)²` for every `z`, i.e. to the positivity claim of part
  (i) itself; the Lean content of part (i) beyond this input is the finiteness,
  the transfer to every `c > 0` and the Lipschitz bounds.  The TeX derives
  positivity differently (lines 57-62: a positive rate of a smooth test through
  `P:variational-unmasked-rate` and `P:compact-original-common-trial`).
  `rayleighFloor_volume` checks that the input is satisfiable (`Γ` = Lebesgue
  measure, an unrestricted covariance outside `H:homog`: it scales like `c^d`,
  i.e. `α = 0`, and is not spatial white noise `δ₀`); `Refutations.SpatialStaticControls` shows it fails
  for `Γ = 0`.
* `S1Bdd α₀ Γ` (sSup corollary only): boundedness above of
  `{I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}`, word for word the boundedness claim of
  `P:variational-positive-scores` at `c = 1` (TeX lines 272-274 of
  `integrated_unmasked_variational.tex`), recorded as a named input.

Implicit hypotheses made explicit: `Γ` locally finite (`H:homog`'s
`Γ_radon`, for Tonelli in `B_Γ`); integrability of every integrand
(conclusions of `convZ_props`, `pairing_bridge`, `ctrl_genuine`); nonemptiness
and boundedness of every Rayleigh set whose supremum is used; `B_Γ(z,z)` is
used through `toReal` only after proving it finite.

Hypotheses carried but unused: `Γ ≠ 0` in both wrappers (part (i) uses it only
through `RayleighFloor`); the fields of `H:homog` other than `Γ_tempered`,
`μ_tempered`, `spectral`, `Γ_radon`, `alpha0_pos`, `alpha0_lt_one`.

Differences from the TeX (statement): `λ_z`, `I_Ψ` and `v_Ψ` are the package's
real-Rayleigh and integral-form quantities (`VariationalDilation`), not
`√(-E_s)` and `E W(Ψ)²` (`P:variational-unmasked-rate`,
`L:compact-raw-profile`, outside Lean); part (ii) is stated in the existential
form (equivalent to the TeX whenever `S_1^pos` is a finite supremum), plus the
sSup form on `S1Bdd`.  Proof route: (1) the cutoff is
`cut_n(t) = χ̃((n+4)t - 1) χ̃((n+4)(1-t) - 1)` with `χ̃ = Real.smoothTransition`
instead of the TeX's `χ(1/(nt)) χ(1/(n(1-t)))` (lines 66-72); (2) dominated
convergence (dominated by `f_a` and by the potential integrand) replaces the
monotone convergence of lines 75-77 and 87-88; (3) the TeX's positive floor
`c₀ ≤ k_n(s)` (line 78) is not needed: `λ_z` is continuous on all of `ℝ`
because `λ_z²` is globally Lipschitz; (4) the mean and cost of `f_n ⊗ z` are
computed as unconditional identities of Bochner integrals (`mean_ctrl`,
`rawCost_ctrl`), and `B_Γ(z,z)` is bridged to the real integral `∫ z U_z` by
Tonelli (`pairing_bridge`); (5) positivity of `B_Γ(z,z)` (lines 88-91) is not
needed for the stated bound and is not formalized.  Lemmas marked "Auxiliary
to the Lean proof route" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.WeakSobolev
public import StratonovichHAMSecondMoment.VariationalDilation
public import StratonovichHAMSecondMoment.VariationalMean
public import StratonovichHAMSecondMoment.TemporalEquilibrium
public import StratonovichHAMSecondMoment.OccupationKernelRow
public import StratonovichHAMSecondMoment.VariationalRate

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace StratonovichHAMSecondMoment.SpatialStaticControls

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open WeakSobolev (IsTestFunction HasWeakGradient IsRayleighTrial rayleighValue rayleighSet
  rayleighRate)
open VariationalDilation (CPos conv mean rawCost rate integratedRate)
open VariationalRate (score1Set S1Bdd S1pos)

variable {d : ℕ}

/-! ### Unit `H^1` pairs and the Rayleigh sets of `c U` -/

/-- A unit `H^1(ℝ^d; ℝ)` pair: `f ∈ L²` with `‖f‖₂ = 1` and an `L²` weak
gradient `g`.  These are the trials of `E:variational-real-rayleigh` without the
potential side condition. -/
def IsUnitH1 (f : Rd d → ℝ) (g : Rd d → Rd d) : Prop :=
  MemLp f 2 volume ∧ MemLp g 2 volume ∧ HasWeakGradient f g ∧ ∫ x, f x ^ 2 = 1

/-- Auxiliary to the Lean proof route.  A test function with `∫ f² = 1` and its
classical gradient form a unit `H^1` pair. -/
theorem isUnitH1_of_test {f : Rd d → ℝ} (hf : IsTestFunction f) (hu : ∫ x, f x ^ 2 = 1) :
    IsUnitH1 f (fun x => (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ f x)) := by
  refine ⟨hf.1.continuous.memLp_of_hasCompactSupport hf.2, ?_,
    VariationalFloor.hasWeakGradient_of_test hf, hu⟩
  have hc : Continuous fun x => (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ f x) :=
    (InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp
      (hf.1.continuous_fderiv (by simp))
  refine hc.memLp_of_hasCompactSupport ?_
  exact (hf.2.fderiv ℝ).comp_left (by simp)

/-- The connection between the two unit-profile predicates of the package: a
real unit test `g ∈ C_c^∞` (`SpatialFourierBound.IsUnitTest`, the profiles of
`P:spatial-smooth-ratio`) with its classical gradient `VariationalFloor.grad g`
is a unit `H^1` pair (`IsUnitH1`, the trials of the Rayleigh sets here). -/
theorem isUnitH1_of_unitTest {g : Rd d → ℝ} (hg : SpatialFourierBound.IsUnitTest g) :
    IsUnitH1 g (VariationalFloor.grad g) :=
  isUnitH1_of_test ⟨hg.1, hg.2.1⟩ hg.2.2

/-- Auxiliary to the Lean proof route.  Unit `H^1` pairs exist (a normalized
smooth bump). -/
theorem exists_isUnitH1 : ∃ f : Rd d → ℝ, ∃ g : Rd d → Rd d, IsUnitH1 f g := by
  let b : ContDiffBump (0 : Rd d) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb0 : (b : Rd d → ℝ) 0 = 1 :=
    b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))
  set I : ℝ := ∫ x, (b : Rd d → ℝ) x ^ 2 with hIdef
  have hI : 0 < I := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (b.continuous.pow 2) (b.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
      (fun x => sq_nonneg _) ?_
    simp [hb0]
  set c : ℝ := (Real.sqrt I)⁻¹ with hcdef
  let f : Rd d → ℝ := fun x => c * (b : Rd d → ℝ) x
  have hf : IsTestFunction f := ⟨contDiff_const.mul b.contDiff, b.hasCompactSupport.mul_left⟩
  have hu : ∫ x, f x ^ 2 = 1 := by
    have e : ∀ x, f x ^ 2 = c ^ 2 * (b : Rd d → ℝ) x ^ 2 := fun x => by simp only [f]; ring
    simp_rw [e]
    rw [integral_const_mul, ← hIdef, hcdef, inv_pow, Real.sq_sqrt hI.le, inv_mul_cancel₀ hI.ne']
  exact ⟨f, _, isUnitH1_of_test hf hu⟩

section bounded
variable {V : Rd d → ℝ} {M : ℝ} (hVc : Continuous V) (hVM : ∀ x, |V x| ≤ M)
include hVc hVM

/-- Auxiliary to the Lean proof route.  For a continuous bounded potential the side condition of
`WeakSobolev.IsRayleighTrial` is automatic: the trials are exactly the unit
`H^1` pairs. -/
theorem isRayleighTrial_iff_of_bounded (f : Rd d → ℝ) (g : Rd d → Rd d) :
    IsRayleighTrial V f g ↔ IsUnitH1 f g := by
  constructor
  · intro h; exact ⟨h.memLp_f, h.memLp_g, h.weakGrad, h.unit⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4, VariationalMean.integrable_pot_of_bounded hVc hVM h1⟩

/-- Auxiliary to the Lean proof route.
For a continuous bounded potential the real Rayleigh set is nonempty. -/
theorem rayleighSet_nonempty_of_bounded : (rayleighSet V).Nonempty := by
  obtain ⟨f, g, h⟩ := exists_isUnitH1 (d := d)
  exact ⟨_, f, g, (isRayleighTrial_iff_of_bounded hVc hVM f g).2 h, rfl⟩

end bounded

/-- Auxiliary to the Lean proof route.  `∫ V f² ≤ M` for a trial with `V ≤ M`. -/
theorem integral_pot_le {V : Rd d → ℝ} {M : ℝ} (hVM : ∀ x, V x ≤ M) {f : Rd d → ℝ}
    {g : Rd d → Rd d} (h : IsRayleighTrial V f g) : ∫ x, V x * f x ^ 2 ≤ M := by
  calc ∫ x, V x * f x ^ 2 ≤ ∫ x, M * f x ^ 2 :=
        integral_mono h.integrable_pot (h.memLp_f.integrable_sq.const_mul M)
          fun x => mul_le_mul_of_nonneg_right (hVM x) (sq_nonneg _)
    _ = M := by rw [integral_const_mul, h.unit, mul_one]

/-- Auxiliary to the Lean proof route.  Every Rayleigh value is at most `M`
when `V ≤ M`; so the Rayleigh set is bounded above. -/
theorem rayleighValue_le {V : Rd d → ℝ} {M : ℝ} (hVM : ∀ x, V x ≤ M) {f : Rd d → ℝ}
    {g : Rd d → Rd d} (h : IsRayleighTrial V f g) : rayleighValue V f g ≤ M := by
  have h1 := integral_pot_le hVM h
  have h2 : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  unfold rayleighValue; linarith

/-- Auxiliary to the Lean proof route.  `BddAbove (rayleighSet V)` for `V ≤ M`. -/
theorem rayleighSet_bddAbove {V : Rd d → ℝ} {M : ℝ} (hVM : ∀ x, V x ≤ M) :
    BddAbove (rayleighSet V) := by
  refine ⟨M, ?_⟩
  rintro q ⟨f, g, h, rfl⟩
  exact rayleighValue_le hVM h

/-! ### The squared rate `λ_U(c)²` and the rate `λ_U(c)` -/

/-- `λ_U(c)² = sup{c ∫ U g² - ‖∇g‖₂² : g ∈ H^1(ℝ^d;ℝ), ‖g‖₂ = 1}` (the
displayed definition of `L:spatial-static-controls`, TeX lines 42-46, with a
general potential `U`; the manuscript's case is `U = U_z = Γ * z`). -/
def lamSq (U : Rd d → ℝ) (c : ℝ) : ℝ := sSup (rayleighSet (fun x => c * U x))

/-- `λ_U(c) = √(λ_U(c)²)` (`WeakSobolev.rayleighRate` of the potential `c U`). -/
def lam (U : Rd d → ℝ) (c : ℝ) : ℝ := rayleighRate (fun x => c * U x)

theorem lam_eq_sqrt (U : Rd d → ℝ) (c : ℝ) : lam U c = Real.sqrt (lamSq U c) := rfl

section potential
variable {U : Rd d → ℝ} {M : ℝ} (hUc : Continuous U) (hU0 : ∀ x, 0 ≤ U x) (hUM : ∀ x, U x ≤ M)
include hUc hU0 hUM

omit hUc in
/-- Auxiliary to the Lean proof route.  `M ≥ 0`. -/
theorem bound_nonneg : 0 ≤ M := (hU0 0).trans (hUM 0)

omit hUc in
/-- Auxiliary to the Lean proof route.  `|c U| ≤ |c| M`. -/
theorem abs_cU_le (c : ℝ) (x : Rd d) : |c * U x| ≤ |c| * M := by
  rw [abs_mul, abs_of_nonneg (hU0 x)]
  exact mul_le_mul_of_nonneg_left (hUM x) (abs_nonneg c)

/-- Auxiliary to the Lean proof route.
The trials of `c U` are the unit `H^1` pairs, for every real `c`. -/
theorem trial_cU_iff (c : ℝ) (f : Rd d → ℝ) (g : Rd d → Rd d) :
    IsRayleighTrial (fun x => c * U x) f g ↔ IsUnitH1 f g :=
  isRayleighTrial_iff_of_bounded (continuous_const.mul hUc)
    (abs_cU_le hU0 hUM c) f g

omit hUc hU0 hUM in
/-- Auxiliary to the Lean proof route.  The Rayleigh value of `c U` is
`c ∫ U f² - ∫ ‖g‖²`. -/
theorem value_cU {c : ℝ} {f : Rd d → ℝ} {g : Rd d → Rd d} :
    rayleighValue (fun x => c * U x) f g = c * (∫ x, U x * f x ^ 2) - ∫ x, ‖g x‖ ^ 2 := by
  unfold rayleighValue
  rw [← integral_const_mul]
  congr 2; funext x; ring

/-- Auxiliary to the Lean proof route.  `0 ≤ ∫ U f² ≤ M` on unit pairs. -/
theorem integral_U_mem {f : Rd d → ℝ} {g : Rd d → Rd d} (h : IsUnitH1 f g) :
    0 ≤ ∫ x, U x * f x ^ 2 ∧ ∫ x, U x * f x ^ 2 ≤ M := by
  have hT : IsRayleighTrial (fun x => 1 * U x) f g := (trial_cU_iff hUc hU0 hUM 1 f g).2 h
  refine ⟨integral_nonneg fun x => mul_nonneg (hU0 x) (sq_nonneg _), ?_⟩
  have := integral_pot_le (V := fun x => 1 * U x) (M := M) (fun x => by simpa using hUM x) hT
  simpa using this

/-- The Rayleigh set of `c U` is nonempty. -/
theorem cU_nonempty (c : ℝ) : (rayleighSet (fun x => c * U x)).Nonempty := by
  obtain ⟨f, g, h⟩ := exists_isUnitH1 (d := d)
  exact ⟨_, f, g, (trial_cU_iff hUc hU0 hUM c f g).2 h, rfl⟩

omit hUc in
/-- The Rayleigh set of `c U` is bounded above by `|c| M`. -/
theorem cU_bddAbove (c : ℝ) : BddAbove (rayleighSet (fun x => c * U x)) :=
  rayleighSet_bddAbove (M := |c| * M) fun x => (le_abs_self _).trans (abs_cU_le hU0 hUM c x)

/-- `λ_U(c)² ≤ |c| M` (finiteness, TeX line 47). -/
theorem lamSq_le (c : ℝ) : lamSq U c ≤ |c| * M := by
  refine csSup_le (cU_nonempty hUc hU0 hUM c) ?_
  rintro q ⟨f, g, h, rfl⟩
  exact rayleighValue_le (fun x => (le_abs_self _).trans (abs_cU_le hU0 hUM c x)) h

/-- Auxiliary to the Lean proof route.  Comparing identical unit tests:
`λ_U(c)² ≤ λ_U(c')² + |c - c'| M` (TeX lines 62-63). -/
theorem lamSq_le_add (c c' : ℝ) : lamSq U c ≤ lamSq U c' + |c - c'| * M := by
  refine csSup_le (cU_nonempty hUc hU0 hUM c) ?_
  rintro q ⟨f, g, h, rfl⟩
  have hu := (trial_cU_iff hUc hU0 hUM c f g).1 h
  have h' := (trial_cU_iff hUc hU0 hUM c' f g).2 hu
  have hq' : rayleighValue (fun x => c' * U x) f g ≤ lamSq U c' :=
    le_csSup (cU_bddAbove hU0 hUM c') ⟨f, g, h', rfl⟩
  obtain ⟨i0, i1⟩ := integral_U_mem hUc hU0 hUM hu
  rw [value_cU] at hq' ⊢
  have : (c - c') * ∫ x, U x * f x ^ 2 ≤ |c - c'| * M :=
    (le_abs_self _).trans (by
      rw [abs_mul, abs_of_nonneg i0]
      exact mul_le_mul_of_nonneg_left i1 (abs_nonneg _))
  nlinarith

/-- `c ↦ λ_U(c)²` is Lipschitz with constant `M = sup U` on all of `ℝ`
(TeX lines 62-63: "comparing identical unit tests makes `λ_z(c)²` Lipschitz
with constant `‖U_z‖_∞`"). -/
theorem lamSq_lip (c c' : ℝ) : |lamSq U c - lamSq U c'| ≤ M * |c - c'| := by
  rw [abs_sub_le_iff]
  have h1 := lamSq_le_add hUc hU0 hUM c c'
  have h2 := lamSq_le_add hUc hU0 hUM c' c
  rw [abs_sub_comm] at h2
  constructor <;> linarith

/-- `c ↦ λ_U(c)²` is nondecreasing (`U ≥ 0`). -/
theorem lamSq_mono {c c' : ℝ} (hcc : c ≤ c') : lamSq U c ≤ lamSq U c' := by
  refine csSup_le (cU_nonempty hUc hU0 hUM c) ?_
  rintro q ⟨f, g, h, rfl⟩
  have hu := (trial_cU_iff hUc hU0 hUM c f g).1 h
  have h' := (trial_cU_iff hUc hU0 hUM c' f g).2 hu
  refine le_trans ?_ (le_csSup (cU_bddAbove hU0 hUM c') ⟨f, g, h', rfl⟩)
  rw [value_cU, value_cU]
  have := (integral_U_mem hUc hU0 hUM hu).1
  nlinarith

/-- `c ↦ λ_U(c)` is nondecreasing. -/
theorem lam_mono {c c' : ℝ} (hcc : c ≤ c') : lam U c ≤ lam U c' :=
  Real.sqrt_le_sqrt (lamSq_mono hUc hU0 hUM hcc)

/-- Auxiliary to the Lean proof route.  `c ↦ λ_U(c)` is continuous on `ℝ`. -/
theorem lam_continuous : Continuous (lam U) := by
  have hM := bound_nonneg hU0 hUM
  have hL : LipschitzWith (Real.toNNReal M) (lamSq U) :=
    LipschitzWith.of_dist_le_mul fun c c' => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM]
      exact lamSq_lip hUc hU0 hUM c c'
  exact Real.continuous_sqrt.comp hL.continuous

/-- Lipschitz bound of `λ_U` on `[c₁, c₂]` from a positive floor
`λ_U(c₁)² > 0` (TeX lines 63-64: "on a positive compact interval its rate has a
positive floor by monotonicity, giving the square-root Lipschitz bound"). -/
theorem lam_lipschitzOn {c₁ c₂ : ℝ} (hpos : 0 < lamSq U c₁) :
    ∃ K : NNReal, LipschitzOnWith K (lam U) (Icc c₁ c₂) := by
  have hM := bound_nonneg hU0 hUM
  set m := Real.sqrt (lamSq U c₁) with hmdef
  have hm : 0 < m := Real.sqrt_pos.2 hpos
  refine ⟨Real.toNNReal (M / (2 * m)), LipschitzOnWith.of_dist_le_mul fun c hc c' hc' => ?_⟩
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity), lam_eq_sqrt,
    lam_eq_sqrt]
  have hA : lamSq U c₁ ≤ lamSq U c := lamSq_mono hUc hU0 hUM hc.1
  have hB : lamSq U c₁ ≤ lamSq U c' := lamSq_mono hUc hU0 hUM hc'.1
  have sA : m ≤ Real.sqrt (lamSq U c) := Real.sqrt_le_sqrt hA
  have sB : m ≤ Real.sqrt (lamSq U c') := Real.sqrt_le_sqrt hB
  have qA := Real.sq_sqrt (hpos.le.trans hA)
  have qB := Real.sq_sqrt (hpos.le.trans hB)
  set p := Real.sqrt (lamSq U c)
  set q := Real.sqrt (lamSq U c')
  have hsum : 0 < p + q := by linarith
  have key : |p - q| * (p + q) = |lamSq U c - lamSq U c'| := by
    rw [← abs_of_pos hsum, ← abs_mul]
    congr 1
    rw [← qA, ← qB]; ring
  have hlip := lamSq_lip hUc hU0 hUM c c'
  have h2m : 2 * m ≤ p + q := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc |p - q| * (2 * m) ≤ |p - q| * (p + q) := mul_le_mul_of_nonneg_left h2m (abs_nonneg _)
    _ ≤ M * |c - c'| := key ▸ hlip

end potential

/-! ### The potential `U_z = Γ * z` and the positivity floor -/

/-- Auxiliary to the Lean proof route.  `Γ * (c z) = c (Γ * z)` (unconditional
identity of Bochner integrals). -/
theorem conv_const_mul (Γ : Measure (Rd d)) (z : Rd d → ℝ) (c : ℝ) :
    conv Γ (fun y => c * z y) = fun x => c * conv Γ z x :=
  funext fun _ => integral_const_mul c _

/-- For a nonnegative test function `z`, a tempered `Γ`, `μ` with the spectral
convention: `y ↦ z(x-y)` is `Γ`-integrable for every `x` (so `U_z(x)` is a
genuine integral), `U_z = Γ * z` is continuous, nonnegative and bounded above
(TeX lines 60-61 use this boundedness, through `P:variational-unmasked-rate`,
which the TeX quotes for "boundedness of this potential"; here it comes from
`VariationalMean.conv_le`, the Gaussian envelope). -/
theorem convZ_props {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {z : Rd d → ℝ} (hz : IsTestFunction z)
    (hz0 : ∀ x, 0 ≤ z x) :
    (∀ x, Integrable (fun y => z (x - y)) Γ) ∧ Continuous (conv Γ z) ∧
      (∀ x, 0 ≤ conv Γ z x) ∧ ∃ M : ℝ, ∀ x, conv Γ z x ≤ M := by
  obtain ⟨B, hB⟩ := hz.1.continuous.bounded_above_of_compact_support hz.2
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hz.2 hz.1 (by simp)
  obtain ⟨R, -, hR⟩ := VariationalFloor.exists_radius_fn hz.2
  set Ψ : ℝ × Rd d → ℝ := fun p => z p.2 with hΨdef
  have hΨc : Continuous Ψ := hz.1.continuous.comp continuous_snd
  have hΨB : ∀ p, |Ψ p| ≤ B := fun p => by simpa [Ψ] using hB p.2
  have hΨL : ∀ p q, |Ψ p - Ψ q| ≤ (L : ℝ) * dist p q := fun p q => by
    have h1 := hL.dist_le_mul p.2 q.2
    rw [Real.dist_eq] at h1
    have h2 : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
    exact h1.trans (mul_le_mul_of_nonneg_left h2 L.2)
  have hΨR : ∀ u y, R < ‖y‖ → Ψ (u, y) = 0 := fun u y hy => hR y hy
  refine ⟨fun x => VariationalMean.conv_integrable hΓt hμt hsp hΨc hΨB hΨR 0 x, ?_,
    fun x => integral_nonneg fun y => hz0 _, ⟨B * Real.exp (R ^ 2 / 2) * VariationalMean.gMass Γ,
      fun x => le_of_abs_le (VariationalMean.conv_le hΓt hμt hsp hΨB hΨR 0 x)⟩⟩
  have := (VariationalMean.convT_continuous hΓt hμt hsp hΨc hΨB hΨL hΨR).comp
    (continuous_const.prodMk continuous_id : Continuous fun x : Rd d => ((0 : ℝ), x))
  exact this

/-- The positivity floor, taken as a named input: the dilation floor lemma of
wave item L6-d at the potential `V = Γ * z`.  For every nonnegative, nonzero
test function `z`, the real Rayleigh set of `U_z = Γ * z` contains a positive
value.  For `U_z` bounded this says exactly that the Rayleigh supremum of `U_z`
is positive.  The manuscript asserts this for every nonzero `Γ` satisfying
`H:homog` (the L6-d route uses `α < 2`); it is not proved here.  It holds for
`Γ` = Lebesgue measure (`rayleighFloor_volume`; outside `H:homog`) and fails for
`Γ = 0`. -/
def RayleighFloor (Γ : Measure (Rd d)) : Prop :=
  ∀ z : Rd d → ℝ, IsTestFunction z → (∀ x, 0 ≤ z x) → z ≠ 0 →
    ∃ q ∈ rayleighSet (conv Γ z), 0 < q

/-- `λ_z(c) = λ_{U_z}(c)` with `U_z = Γ * z` (TeX lines 42-46). -/
def lamZ (Γ : Measure (Rd d)) (z : Rd d → ℝ) (c : ℝ) : ℝ := lam (conv Γ z) c

/-- Part (i) of `L:spatial-static-controls` (TeX lines 41-49), general form
(tempered `Γ`, `μ`, spectral convention, the floor `RayleighFloor Γ`), for a
nonnegative nonzero test function `z`: (a) for every real `c` the Rayleigh set
of `c U_z` is nonempty and bounded above; (b) for `c > 0`, `λ_z(c)² > 0`,
`λ_z(c) > 0` and `λ_z(c)² = (√·)²`; (c) for every upper bound `M` of `U_z`
(in particular `‖U_z‖_∞`), `|λ_z(c)² - λ_z(c')²| ≤ M |c - c'|`, and such an `M`
exists; (d) `λ_z` is Lipschitz on every compact positive interval
`[c₁, c₂]`, `c₁ > 0`.  The floor is used only for (b) and (d). -/
theorem static_rate {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) (hfloor : RayleighFloor Γ) {z : Rd d → ℝ}
    (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) :
    (∀ c : ℝ, (rayleighSet (fun x => c * conv Γ z x)).Nonempty ∧
      BddAbove (rayleighSet (fun x => c * conv Γ z x))) ∧
    (∀ c : ℝ, 0 < c → 0 < lamSq (conv Γ z) c ∧ 0 < lamZ Γ z c ∧
      lamZ Γ z c ^ 2 = lamSq (conv Γ z) c) ∧
    (∃ M : ℝ, ∀ x, conv Γ z x ≤ M) ∧
    (∀ M : ℝ, (∀ x, conv Γ z x ≤ M) → ∀ c c' : ℝ,
      |lamSq (conv Γ z) c - lamSq (conv Γ z) c'| ≤ M * |c - c'|) ∧
    (∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ K : NNReal, LipschitzOnWith K (lamZ Γ z) (Icc c₁ c₂)) := by
  obtain ⟨-, hUc, hU0, ⟨M, hUM⟩⟩ := convZ_props hΓt hμt hsp hz hz0
  have hpos : ∀ c : ℝ, 0 < c → 0 < lamSq (conv Γ z) c := by
    intro c hc
    have hzc : IsTestFunction (fun y => c * z y) := ⟨contDiff_const.mul hz.1, hz.2.mul_left⟩
    have hne : (fun y => c * z y) ≠ 0 := by
      intro h; apply hzne; funext y
      have := congrFun h y
      simpa [hc.ne'] using this
    obtain ⟨q, hq, hq0⟩ := hfloor _ hzc (fun y => mul_nonneg hc.le (hz0 y)) hne
    rw [conv_const_mul] at hq
    exact hq0.trans_le (le_csSup (cU_bddAbove hU0 hUM c) hq)
  refine ⟨fun c => ⟨cU_nonempty hUc hU0 hUM c, cU_bddAbove hU0 hUM c⟩, fun c hc => ?_,
    ⟨M, hUM⟩, fun M' hM' c c' => lamSq_lip hUc hU0 hM' c c', fun c₁ c₂ hc₁ =>
      lam_lipschitzOn hUc hU0 hUM (hpos c₁ hc₁)⟩
  have h := hpos c hc
  exact ⟨h, Real.sqrt_pos.2 h, Real.sq_sqrt h.le⟩

/-! ### The temporal cutoffs `f_n` -/

/-- The smooth cutoff `cut_n(t) = χ̃((n+4)t - 1) χ̃((n+4)(1-t) - 1)` with
`χ̃ = Real.smoothTransition` (`0` on `(-∞,0]`, `1` on `[1,∞)`).  Lean route: it
replaces the manuscript's `χ(1/(nt)) χ(1/(n(1-t)))` (TeX lines 66-72; `χ` from
`P:variational-remove-mask`); both are smooth, in `[0,1]`, vanish near the
endpoints and equal `1` on compact subsets of `(0,1)` for large `n`, which is
all the proof uses. -/
def cut (n : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 4) * t - 1) *
    Real.smoothTransition (((n : ℝ) + 4) * (1 - t) - 1)

/-- `f_n = f_a · cut_n` (TeX lines 70-72, with the cutoff `cut_n`); `f_a` is
`TemporalEquilibrium.density a`. -/
def fn (a : ℝ) (n : ℕ) (t : ℝ) : ℝ := TemporalEquilibrium.density a t * cut n t

/-- Auxiliary to the Lean proof route.  `cut_n` is smooth. -/
theorem cut_contDiff (n : ℕ) : ContDiff ℝ ∞ (cut n) := by
  unfold cut
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

/-- Auxiliary to the Lean proof route.  `0 ≤ cut_n ≤ 1`. -/
theorem cut_mem (n : ℕ) (t : ℝ) : 0 ≤ cut n t ∧ cut n t ≤ 1 := by
  unfold cut
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    by nlinarith [Real.smoothTransition.le_one (((n : ℝ) + 4) * t - 1),
      Real.smoothTransition.le_one (((n : ℝ) + 4) * (1 - t) - 1),
      Real.smoothTransition.nonneg (((n : ℝ) + 4) * t - 1),
      Real.smoothTransition.nonneg (((n : ℝ) + 4) * (1 - t) - 1)]⟩

/-- Auxiliary to the Lean proof route.  `cut_n` vanishes off
`(1/(n+4), 1 - 1/(n+4))`. -/
theorem cut_eq_zero (n : ℕ) {t : ℝ}
    (ht : t ∉ Ioo (1 / ((n : ℝ) + 4)) (1 - 1 / ((n : ℝ) + 4))) : cut n t = 0 := by
  have hN : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  simp only [mem_Ioo, not_and_or, not_lt] at ht
  unfold cut
  rcases ht with h | h
  · have : ((n : ℝ) + 4) * t - 1 ≤ 0 := by
      rw [le_div_iff₀ hN] at h
      linarith
    rw [Real.smoothTransition.zero_of_nonpos this, zero_mul]
  · have : ((n : ℝ) + 4) * (1 - t) - 1 ≤ 0 := by
      have h' : 1 - t ≤ 1 / ((n : ℝ) + 4) := by linarith
      rw [le_div_iff₀ hN] at h'
      linarith
    rw [Real.smoothTransition.zero_of_nonpos this, mul_zero]

/-- Auxiliary to the Lean proof route.  For `t ∈ (0,1)`, `cut_n(t) = 1` for all
large `n`. -/
theorem cut_eventually_one {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, cut n t = 1 := by
  have h1t : 0 < 1 - t := by linarith [ht.2]
  obtain ⟨n0, hn0⟩ := exists_nat_ge (2 / t + 2 / (1 - t))
  refine eventually_atTop.2 ⟨n0, fun n hn => ?_⟩
  have hn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 2 / t ≤ n := by
    have : 0 ≤ 2 / (1 - t) := by positivity
    linarith
  have hb : 2 / (1 - t) ≤ n := by
    have : 0 ≤ 2 / t := div_nonneg (by norm_num) ht.1.le
    linarith
  rw [div_le_iff₀ ht.1] at ha
  rw [div_le_iff₀ h1t] at hb
  have e1 : 1 ≤ ((n : ℝ) + 4) * t - 1 := by nlinarith [ht.1]
  have e2 : 1 ≤ ((n : ℝ) + 4) * (1 - t) - 1 := by nlinarith
  unfold cut
  rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.one_of_one_le e2, one_mul]

/-- Auxiliary to the Lean proof route.  `cut_n(1/2) = 1`. -/
theorem cut_half (n : ℕ) : cut n (1 / 2) = 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : 1 ≤ ((n : ℝ) + 4) * (1 / 2) - 1 := by linarith
  have e2 : 1 ≤ ((n : ℝ) + 4) * (1 - 1 / 2) - 1 := by linarith
  unfold cut
  rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.one_of_one_le e2, one_mul]

section cutoff
variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
include ha0 ha1

omit ha0 ha1 in
/-- `f_n` is smooth on `ℝ` (it vanishes near both endpoints; TeX line 73). -/
theorem fn_contDiff (n : ℕ) : ContDiff ℝ ∞ (fn a n) := by
  have hN : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  have hN1 : (0 : ℝ) < 1 / ((n : ℝ) + 4) := by positivity
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · have hp : ContDiffAt ℝ ∞ (fun t : ℝ => t * (1 - t)) t := by fun_prop
    have hne : t * (1 - t) ≠ 0 := (mul_pos ht.1 (by linarith [ht.2])).ne'
    have hd := (hp.rpow_const_of_ne hne (p := -((1 - a) / 2))).div_const
      (Real.Gamma ((1 - a) / 2) * Real.Gamma (1 - (1 - a) / 2))
    exact hd.mul (cut_contDiff n).contDiffAt
  · have hz : fn a n =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      simp only [mem_Ioo, not_and_or, not_lt] at ht
      have hev : ∀ᶠ s in 𝓝 t, s ∉ Ioo (1 / ((n : ℝ) + 4)) (1 - 1 / ((n : ℝ) + 4)) := by
        rcases ht with h | h
        · filter_upwards [Iio_mem_nhds (show t < 1 / ((n : ℝ) + 4) by linarith)] with s hs
          exact fun h' => (lt_irrefl _ (hs.trans h'.1))
        · filter_upwards [Ioi_mem_nhds (show 1 - 1 / ((n : ℝ) + 4) < t by linarith)] with s hs
          exact fun h' => (lt_irrefl _ (hs.trans h'.2))
      filter_upwards [hev] with s hs
      simp only [fn, cut_eq_zero n hs, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz

omit ha0 ha1 in
/-- Auxiliary to the Lean proof route.  `f_n` is continuous. -/
theorem fn_continuous (n : ℕ) : Continuous (fn a n) := (fn_contDiff n).continuous

/-- `f_n ≥ 0`. -/
theorem fn_nonneg (n : ℕ) (t : ℝ) : 0 ≤ fn a n t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · exact mul_nonneg (TemporalEquilibrium.density_pos ha0 ha1 t ht).le (cut_mem n t).1
  · have : t ∉ Ioo (1 / ((n : ℝ) + 4)) (1 - 1 / ((n : ℝ) + 4)) := fun h =>
      ht ⟨lt_trans (by positivity) h.1, lt_of_lt_of_le h.2 (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 4) := by positivity
        linarith)⟩
    simp only [fn, cut_eq_zero n this, mul_zero, le_refl]

/-- `f_n ≤ f_a` on `(0,1)`. -/
theorem fn_le_density (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    fn a n t ≤ TemporalEquilibrium.density a t :=
  mul_le_of_le_one_right (TemporalEquilibrium.density_pos ha0 ha1 t ht).le (cut_mem n t).2

omit ha0 ha1 in
/-- `f_n(t) → f_a(t)` for `t ∈ (0,1)` (indeed `f_n(t) = f_a(t)` for large `n`). -/
theorem fn_tendsto {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => fn a n t) atTop (𝓝 (TemporalEquilibrium.density a t)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [cut_eventually_one ht] with n hn
  simp only [fn, hn, mul_one]

omit ha0 ha1 in
/-- `f_n` vanishes off `(1/(n+4), 1 - 1/(n+4))`. -/
theorem fn_eq_zero (n : ℕ) {t : ℝ}
    (ht : t ∉ Ioo (1 / ((n : ℝ) + 4)) (1 - 1 / ((n : ℝ) + 4))) : fn a n t = 0 := by
  simp only [fn, cut_eq_zero n ht, mul_zero]

/-- `f_n(1/2) > 0`. -/
theorem fn_half_pos (n : ℕ) : 0 < fn a n (1 / 2) := by
  rw [fn, cut_half, mul_one]
  exact TemporalEquilibrium.density_pos ha0 ha1 _ ⟨by norm_num, by norm_num⟩

end cutoff

/-! ### The controls `Ψ_n = f_n ⊗ z` -/

/-- `Ψ_n(t,x) = f_n(t) z(x)` (TeX line 74). -/
def ctrl (a : ℝ) (n : ℕ) (z : Rd d → ℝ) : ℝ × Rd d → ℝ := fun p => fn a n p.1 * z p.2

/-- `Ψ_n ∈ C_pos` for a nonnegative nonzero test function `z` (TeX lines 73-75). -/
theorem ctrl_mem {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) {z : Rd d → ℝ}
    (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) : ctrl a n z ∈ CPos d := by
  set N : ℝ := (n : ℝ) + 4 with hNdef
  have hN1 : (0 : ℝ) < 1 / N := by positivity
  have hN2 : 1 / N ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsupp : ∀ p : ℝ × Rd d, p.1 ∉ Icc (1 / N) (1 - 1 / N) → ctrl a n z p = 0 := by
    intro p hp
    have : p.1 ∉ Ioo (1 / N) (1 - 1 / N) := fun h => hp (Ioo_subset_Icc_self h)
    simp only [ctrl, fn_eq_zero n this, zero_mul]
  refine ⟨(fn_contDiff n).comp contDiff_fst |>.mul (hz.1.comp contDiff_snd), ?_, ?_,
    fun p => mul_nonneg (fn_nonneg ha0 ha1 n _) (hz0 _), ?_⟩
  · refine HasCompactSupport.intro (K := Icc (1 / N) (1 - 1 / N) ×ˢ tsupport z)
      (isCompact_Icc.prod hz.2) fun p hp => ?_
    rw [mem_prod, not_and_or] at hp
    rcases hp with h | h
    · exact hsupp p h
    · simp only [ctrl, image_eq_zero_of_notMem_tsupport h, mul_zero]
  · have h1 : tsupport (ctrl a n z) ⊆ Icc (1 / N) (1 - 1 / N) ×ˢ (univ : Set (Rd d)) := by
      refine closure_minimal (fun p hp => ?_) (isClosed_Icc.prod isClosed_univ)
      refine ⟨?_, mem_univ _⟩
      by_contra h
      exact hp (hsupp p h)
    exact h1.trans (prod_mono (fun t ht => ⟨lt_of_lt_of_le hN1 ht.1, by linarith [ht.2]⟩)
      subset_rfl)
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 hzne
    intro h
    have := congrFun h ((1 / 2 : ℝ), x)
    simp only [ctrl, Pi.zero_apply] at this hx
    exact hx ((mul_eq_zero.1 this).resolve_left (fn_half_pos ha0 ha1 n).ne')

/-! ### Mean, rate and cost of `Ψ_n` -/

/-- `k_n(s) = ∫_0^1 |s-t|^{-a} f_n(t) dt` (TeX line 71). -/
def kn (a : ℝ) (n : ℕ) (s : ℝ) : ℝ := ∫ t in Ioo (0 : ℝ) 1, |s - t| ^ (-a) * fn a n t

/-- The mean of `Ψ_n` is `k_n(s) U_z` (TeX lines 78-79; an unconditional identity
of Bochner integrals, for every `Γ`, `a`, `n`, `z`, `s`). -/
theorem mean_ctrl (a : ℝ) (Γ : Measure (Rd d)) (n : ℕ) (z : Rd d → ℝ) (s : ℝ) :
    mean a Γ (ctrl a n z) s = fun x => kn a n s * conv Γ z x := by
  funext x
  have e : ∀ u, conv Γ (fun y => ctrl a n z (u, y)) x = fn a n u * conv Γ z x := by
    intro u
    simp only [ctrl, conv]
    exact integral_const_mul _ _
  simp only [mean, e, kn]
  rw [← integral_mul_const]
  congr 1; funext u; ring

/-- The rate of `Ψ_n` at `s` is `λ_z(k_n(s))` (TeX lines 79-81). -/
theorem rate_ctrl (a : ℝ) (Γ : Measure (Rd d)) (n : ℕ) (z : Rd d → ℝ) (s : ℝ) :
    rate a Γ (ctrl a n z) s = lamZ Γ z (kn a n s) := by
  rw [rate, mean_ctrl]; rfl

/-- The Gaussian cost of `Ψ_n` in its integral form (TeX lines 83-86):
`v_{Ψ_n} = (∫_0^1 f_n k_n) · ∫ z U_z` (unconditional identity). -/
theorem rawCost_ctrl (a : ℝ) (Γ : Measure (Rd d)) (n : ℕ) (z : Rd d → ℝ) :
    rawCost a Γ (ctrl a n z) =
      (∫ σ in Ioo (0 : ℝ) 1, fn a n σ * kn a n σ) * ∫ x, z x * conv Γ z x := by
  have e : ∀ σ, ∫ x, ctrl a n z (σ, x) * mean a Γ (ctrl a n z) σ x =
      (fn a n σ * kn a n σ) * ∫ x, z x * conv Γ z x := by
    intro σ
    rw [mean_ctrl, ← integral_const_mul]
    congr 1; funext x; simp only [ctrl]; ring
  simp only [rawCost, e]
  exact integral_mul_const _ _

/-! ### The weights `k_n` -/

section kn
variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
include ha0 ha1

/-- Auxiliary to the Lean proof route.
The integrand of `k_n(s)` is integrable on `(0,1)` for `s ∈ [0,1]`
(dominated by the integrand of `E:temporal-equilibrium-potential`). -/
theorem kn_integrableOn (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun t => |s - t| ^ (-a) * fn a n t) (Ioo 0 1) := by
  have hP := (TemporalEquilibrium.potential_eq_one ha0 ha1 s hs).1
  refine hP.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_)
  · exact ((by fun_prop : Measurable fun t : ℝ => |s - t| ^ (-a)).mul
      (fn_continuous n).measurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (fn_nonneg ha0 ha1 n t))]
    exact mul_le_mul_of_nonneg_left (fn_le_density ha0 ha1 n ht)
      (Real.rpow_nonneg (abs_nonneg _) _)

/-- Auxiliary to the Lean proof route.  `k_n ≥ 0`. -/
theorem kn_nonneg (n : ℕ) (s : ℝ) : 0 ≤ kn a n s :=
  setIntegral_nonneg measurableSet_Ioo fun t _ =>
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (fn_nonneg ha0 ha1 n t)

/-- `k_n(s) ≤ 1` on `[0,1]` (`f_n ≤ f_a` and
`E:temporal-equilibrium-potential`, TeX lines 77-78). -/
theorem kn_le_one (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : kn a n s ≤ 1 := by
  have hP := TemporalEquilibrium.potential_eq_one ha0 ha1 s hs
  rw [← hP.2]
  exact setIntegral_mono_on (kn_integrableOn ha0 ha1 n hs) hP.1 measurableSet_Ioo fun t ht =>
    mul_le_mul_of_nonneg_left (fn_le_density ha0 ha1 n ht) (Real.rpow_nonneg (abs_nonneg _) _)

/-- `k_n(s) → 1` for `s ∈ [0,1]` (TeX lines 75-77; Lean route: dominated
convergence with the integrand of `E:temporal-equilibrium-potential` as
dominating function, instead of monotone convergence). -/
theorem kn_tendsto {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => kn a n s) atTop (𝓝 1) := by
  have hP := TemporalEquilibrium.potential_eq_one ha0 ha1 s hs
  rw [← hP.2]
  refine tendsto_integral_of_dominated_convergence
    (fun t => |s - t| ^ (-a) * TemporalEquilibrium.density a t)
    (fun n => (kn_integrableOn ha0 ha1 n hs).aestronglyMeasurable) hP.1
    (fun n => ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => (fn_tendsto ht).const_mul _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (fn_nonneg ha0 ha1 n t))]
  exact mul_le_mul_of_nonneg_left (fn_le_density ha0 ha1 n ht)
    (Real.rpow_nonneg (abs_nonneg _) _)

omit ha0 ha1 in
/-- Auxiliary to the Lean proof route.  `s ↦ k_n(s)` is strongly measurable. -/
theorem kn_measurable (n : ℕ) : StronglyMeasurable (kn a n) := by
  have hm : Measurable (Function.uncurry fun s t : ℝ => |s - t| ^ (-a) * fn a n t) := by
    have : Measurable fun p : ℝ × ℝ => |p.1 - p.2| ^ (-a) * fn a n p.2 :=
      (by fun_prop : Measurable fun p : ℝ × ℝ => |p.1 - p.2| ^ (-a)).mul
        ((fn_continuous n).measurable.comp measurable_snd)
    exact this
  exact hm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioo (0 : ℝ) 1))

/-- Auxiliary to the Lean proof route.
`f_n k_n` is integrable on `(0,1)`, with `0 ≤ f_n k_n ≤ f_a` there. -/
theorem fnkn_integrableOn (n : ℕ) :
    IntegrableOn (fun σ => fn a n σ * kn a n σ) (Ioo 0 1) := by
  refine (TemporalEquilibrium.density_integrableOn ha0 ha1).mono'
    ((fn_continuous n).measurable.stronglyMeasurable.mul (kn_measurable n)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fn_nonneg ha0 ha1 n σ) (kn_nonneg ha0 ha1 n σ))]
  calc fn a n σ * kn a n σ ≤ fn a n σ * 1 :=
        mul_le_mul_of_nonneg_left (kn_le_one ha0 ha1 n (Ioo_subset_Icc_self hσ))
          (fn_nonneg ha0 ha1 n σ)
    _ ≤ _ := by rw [mul_one]; exact fn_le_density ha0 ha1 n hσ

/-- `∫_0^1 f_n k_n → M_a` (TeX lines 87-88: "its time integrand increases to
`f_a`"; Lean route: dominated convergence by `f_a`). -/
theorem fnkn_tendsto :
    Tendsto (fun n => ∫ σ in Ioo (0 : ℝ) 1, fn a n σ * kn a n σ) atTop
      (𝓝 (TemporalEquilibrium.mass a)) := by
  refine tendsto_integral_of_dominated_convergence (TemporalEquilibrium.density a)
    (fun n => (fnkn_integrableOn ha0 ha1 n).aestronglyMeasurable)
    (TemporalEquilibrium.density_integrableOn ha0 ha1)
    (fun n => ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fn_nonneg ha0 ha1 n σ)
      (kn_nonneg ha0 ha1 n σ))]
    calc fn a n σ * kn a n σ ≤ fn a n σ * 1 :=
          mul_le_mul_of_nonneg_left (kn_le_one ha0 ha1 n (Ioo_subset_Icc_self hσ))
            (fn_nonneg ha0 ha1 n σ)
      _ ≤ _ := by rw [mul_one]; exact fn_le_density ha0 ha1 n hσ
  · have := (fn_tendsto (a := a) hσ).mul (kn_tendsto ha0 ha1 (Ioo_subset_Icc_self hσ))
    simpa only [mul_one] using this

end kn

/-! ### The physical pairing `B_Γ(z,z)` -/

/-- Auxiliary to the Lean proof route.  `z` as a `[0,∞]`-valued function, the argument of
`OccupationKernelRow.pairing` (`B_Γ` of `E:spatial-physical-pair`). -/
def zE (z : Rd d → ℝ) : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal (z x)

/-- The bridge between the extended nonnegative pairing `B_Γ(z,z)` of
`E:spatial-physical-pair` (`OccupationKernelRow.pairing`) and the real integral
`∫ z U_z` that appears in the cost: for a locally finite tempered `Γ` (with a
tempered `μ` and the spectral convention) and a nonnegative test function `z`,
`x ↦ z(x) U_z(x)` is integrable, `B_Γ(z,z) = ofReal (∫ z U_z)`, so
`B_Γ(z,z) < ∞` and `B_Γ(z,z).toReal = ∫ z U_z ≥ 0` (TeX line 88: "the spatial
factor is finite"). -/
theorem pairing_bridge {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) (hΓloc : IsLocallyFiniteMeasure Γ) {z : Rd d → ℝ}
    (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) :
    Integrable (fun x => z x * conv Γ z x) ∧
      OccupationKernelRow.pairing Γ (zE z) (zE z) = ENNReal.ofReal (∫ x, z x * conv Γ z x) ∧
      OccupationKernelRow.pairing Γ (zE z) (zE z) ≠ ⊤ ∧
      (OccupationKernelRow.pairing Γ (zE z) (zE z)).toReal = ∫ x, z x * conv Γ z x ∧
      0 ≤ ∫ x, z x * conv Γ z x := by
  obtain ⟨hint, hUc, hU0, M, hUM⟩ := convZ_props hΓt hμt hsp hz hz0
  have : IsLocallyFiniteMeasure Γ := hΓloc
  have hzI : Integrable z := hz.1.continuous.integrable_of_hasCompactSupport hz.2
  have hzU : Integrable (fun x => z x * conv Γ z x) := by
    have := hzI.bdd_mul (c := M) hUc.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hU0 x)]; exact hUM x)
    simpa only [mul_comm] using this
  have hnn : 0 ≤ ∫ x, z x * conv Γ z x := integral_nonneg fun x => mul_nonneg (hz0 x) (hU0 x)
  have hmeas : Measurable fun p : Rd d × Rd d => zE z p.1 * zE z (p.1 - p.2) :=
    ((hz.1.continuous.measurable.comp measurable_fst).ennreal_ofReal).mul
      ((hz.1.continuous.measurable.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal)
  have inner : ∀ x, ∫⁻ y, zE z x * zE z (x - y) ∂Γ = ENNReal.ofReal (z x * conv Γ z x) := by
    intro x
    simp only [zE]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (hz0 x)]
    congr 1
    exact (ofReal_integral_eq_lintegral_ofReal (hint x) (ae_of_all _ fun y => hz0 _)).symm
  have hP : OccupationKernelRow.pairing Γ (zE z) (zE z) =
      ENNReal.ofReal (∫ x, z x * conv Γ z x) := by
    unfold OccupationKernelRow.pairing OccupationKernelRow.pairMeasure
    rw [lintegral_prod _ hmeas.aemeasurable]
    simp only [inner]
    exact (ofReal_integral_eq_lintegral_ofReal hzU
      (ae_of_all _ fun x => mul_nonneg (hz0 x) (hU0 x))).symm
  refine ⟨hzU, hP, by rw [hP]; exact ENNReal.ofReal_ne_top, by rw [hP, ENNReal.toReal_ofReal hnn],
    hnn⟩

/-- The bridge between the two forms of the physical pairing `B_Γ` of
`E:spatial-physical-pair`: the extended nonnegative pairing
`OccupationKernelRow.pairing` (used here) and the real iterated integral
`SpatialFourierBound.spatialPair Γ F G = ∫ (∫ F(x) G(x - y) dx) Γ(dy)` (used by
`P:spatial-smooth-ratio`).  For a locally finite `Γ` and continuous,
nonnegative, compactly supported `F`, `G`: the inner integral is
`Γ`-integrable, `B_Γ(F,G) = ofReal (spatialPair Γ F G)`, and
`B_Γ(F,G).toReal = spatialPair Γ F G` (Tonelli). -/
theorem pairing_eq_spatialPair {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    {F G : Rd d → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F) (hF0 : ∀ x, 0 ≤ F x)
    (hGc : Continuous G) (hGs : HasCompactSupport G) (hG0 : ∀ x, 0 ≤ G x) :
    Integrable (fun y => ∫ x, F x * G (x - y)) Γ ∧
      OccupationKernelRow.pairing Γ (fun x => ENNReal.ofReal (F x))
          (fun x => ENNReal.ofReal (G x)) =
        ENNReal.ofReal (SpatialFourierBound.spatialPair Γ F G) ∧
      (OccupationKernelRow.pairing Γ (fun x => ENNReal.ofReal (F x))
          (fun x => ENNReal.ofReal (G x))).toReal = SpatialFourierBound.spatialPair Γ F G := by
  obtain ⟨BG, hBG⟩ := hGc.bounded_above_of_compact_support hGs
  obtain ⟨RF, -, hRF⟩ := VariationalFloor.exists_radius_fn hFs
  obtain ⟨RG, -, hRG⟩ := VariationalFloor.exists_radius_fn hGs
  have hFi : Integrable F volume := hFc.integrable_of_hasCompactSupport hFs
  have hin : ∀ y, Integrable (fun x => F x * G (x - y)) volume := fun y =>
    (hFc.mul (hGc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hFs.mul_right
  have hKc : Continuous fun y => ∫ x, F x * G (x - y) := by
    refine continuous_of_dominated (bound := fun x => ‖F x‖ * BG)
      (fun y => (hFc.mul (hGc.comp (continuous_id.sub continuous_const))).aestronglyMeasurable)
      (fun y => Filter.Eventually.of_forall fun x => ?_) (hFi.norm.mul_const BG)
      (Filter.Eventually.of_forall fun x =>
        continuous_const.mul (hGc.comp (continuous_const.sub continuous_id)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hBG _) (norm_nonneg _)
  have hKs : HasCompactSupport fun y => ∫ x, F x * G (x - y) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) (RF + RG)) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : RF < ‖x‖
    · simp [hRF x hx]
    · have : RG < ‖x - y‖ := by
        have := norm_sub_norm_le y x
        rw [← norm_neg (x - y), neg_sub]
        linarith
      simp [hRG _ this]
  have hKi : Integrable (fun y => ∫ x, F x * G (x - y)) Γ :=
    hKc.integrable_of_hasCompactSupport hKs
  have hK0 : ∀ y, 0 ≤ ∫ x, F x * G (x - y) := fun y =>
    integral_nonneg fun x => mul_nonneg (hF0 x) (hG0 _)
  have hmeas : AEMeasurable (fun p : Rd d × Rd d =>
      ENNReal.ofReal (F p.1) * ENNReal.ofReal (G (p.1 - p.2)))
      (OccupationKernelRow.pairMeasure Γ) :=
    (((hFc.measurable.comp measurable_fst).ennreal_ofReal).mul
      ((hGc.measurable.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal)).aemeasurable
  have hP : OccupationKernelRow.pairing Γ (fun x => ENNReal.ofReal (F x))
      (fun x => ENNReal.ofReal (G x)) =
      ENNReal.ofReal (SpatialFourierBound.spatialPair Γ F G) := by
    unfold OccupationKernelRow.pairing
    rw [OccupationKernelRow.pairMeasure, lintegral_prod_symm _ hmeas]
    have inner : ∀ y, ∫⁻ x, ENNReal.ofReal (F x) * ENNReal.ofReal (G (x - y)) =
        ENNReal.ofReal (∫ x, F x * G (x - y)) := by
      intro y
      simp_rw [← ENNReal.ofReal_mul (hF0 _)]
      exact (ofReal_integral_eq_lintegral_ofReal (hin y)
        (Filter.Eventually.of_forall fun x => mul_nonneg (hF0 x) (hG0 _))).symm
    simp only [inner]
    exact (ofReal_integral_eq_lintegral_ofReal hKi (Filter.Eventually.of_forall hK0)).symm
  refine ⟨hKi, hP, ?_⟩
  rw [hP]; exact ENNReal.toReal_ofReal (integral_nonneg hK0)

/-! ### The static score bound -/

section score
variable {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
  (hsp : IsSpectralMeasure Γ μ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : Rd d → ℝ}
  (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x)
include hΓt hμt hsp ha0 ha1 hz hz0

/-- `I_{Ψ_n} → λ_z(1)` (TeX lines 78-81: the rate at `s` is `λ_z(k_n(s))`,
converging to `λ_z(1)` and bounded by it; dominated convergence).  Lean
route: continuity of `λ_z` on `ℝ` (from the global Lipschitz bound of `λ_z²`)
replaces the TeX's positive floor `c₀ ≤ k_n`; no floor is needed here. -/
theorem integratedRate_tendsto :
    Tendsto (fun n => integratedRate a Γ (ctrl a n z)) atTop (𝓝 (lamZ Γ z 1)) := by
  obtain ⟨-, hUc, hU0, M, hUM⟩ := convZ_props hΓt hμt hsp hz hz0
  have hcont : Continuous (lamZ Γ z) := lam_continuous hUc hU0 hUM
  have e : ∀ n, integratedRate a Γ (ctrl a n z) =
      ∫ s in Ioo (0 : ℝ) 1, lamZ Γ z (kn a n s) := by
    intro n; simp only [integratedRate, rate_ctrl]
  have hlim : lamZ Γ z 1 = ∫ _ in Ioo (0 : ℝ) 1, lamZ Γ z 1 := by
    simp
  simp only [e]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun _ => lamZ Γ z 1)
    (fun n => (hcont.comp_stronglyMeasurable (kn_measurable n)).aestronglyMeasurable)
    (integrableOn_const (by simp [Real.volume_Ioo]))
    (fun n => ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs =>
      (hcont.tendsto 1).comp (kn_tendsto ha0 ha1 (Ioo_subset_Icc_self hs)))
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ lamZ Γ z (kn a n s) from Real.sqrt_nonneg _)]
  exact lam_mono hUc hU0 hUM (kn_le_one ha0 ha1 n (Ioo_subset_Icc_self hs))

/-- Auxiliary to the Lean proof route.
The rate of `Ψ_n` is integrable on `(0,1)` and every Rayleigh set
`R_{Ψ_n,s}` is nonempty and bounded above, so `I_{Ψ_n}` is a genuine integral of
genuine suprema; every spatial and temporal integrand of `v_{Ψ_n}` is
integrable. -/
theorem ctrl_genuine (n : ℕ) :
    (∀ s, (rayleighSet (mean a Γ (ctrl a n z) s)).Nonempty ∧
      BddAbove (rayleighSet (mean a Γ (ctrl a n z) s))) ∧
    IntegrableOn (rate a Γ (ctrl a n z)) (Ioo 0 1) ∧
    (∀ σ, Integrable (fun x => ctrl a n z (σ, x) * mean a Γ (ctrl a n z) σ x)) ∧
    IntegrableOn (fun σ => ∫ x, ctrl a n z (σ, x) * mean a Γ (ctrl a n z) σ x) (Ioo 0 1) := by
  obtain ⟨-, hUc, hU0, M, hUM⟩ := convZ_props hΓt hμt hsp hz hz0
  have hcont : Continuous (lamZ Γ z) := lam_continuous hUc hU0 hUM
  have hzU : Integrable (fun x => z x * conv Γ z x) := by
    obtain ⟨hint, -⟩ := convZ_props hΓt hμt hsp hz hz0
    have hzI : Integrable z := hz.1.continuous.integrable_of_hasCompactSupport hz.2
    have := hzI.bdd_mul (c := M) hUc.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hU0 x)]; exact hUM x)
    simpa only [mul_comm] using this
  have hin : ∀ σ, (fun x => ctrl a n z (σ, x) * mean a Γ (ctrl a n z) σ x) =
      fun x => (fn a n σ * kn a n σ) * (z x * conv Γ z x) := by
    intro σ; funext x; rw [mean_ctrl]; simp only [ctrl]; ring
  refine ⟨fun s => ?_, ?_, fun σ => ?_, ?_⟩
  · rw [mean_ctrl]
    exact ⟨cU_nonempty hUc hU0 hUM _, cU_bddAbove hU0 hUM _⟩
  · have e : rate a Γ (ctrl a n z) = fun s => lamZ Γ z (kn a n s) := funext (rate_ctrl a Γ n z)
    rw [e]
    refine (integrableOn_const (C := lamZ Γ z 1) (by simp [Real.volume_Ioo])).mono'
      (hcont.comp_stronglyMeasurable (kn_measurable n)).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ lamZ Γ z (kn a n s) from Real.sqrt_nonneg _)]
    exact lam_mono hUc hU0 hUM (kn_le_one ha0 ha1 n (Ioo_subset_Icc_self hs))
  · rw [hin]; exact hzU.const_mul _
  · have e : (fun σ => ∫ x, ctrl a n z (σ, x) * mean a Γ (ctrl a n z) σ x) =
        fun σ => (fn a n σ * kn a n σ) * ∫ x, z x * conv Γ z x := by
      funext σ; rw [hin, integral_const_mul]
    rw [e]
    exact (fnkn_integrableOn ha0 ha1 n).mul_const _

/-- The scores of `Ψ_n` converge:
`I_{Ψ_n} - v_{Ψ_n}/2 → λ_z(1) - (M_a/2) B_Γ(z,z)`, with
`B_Γ(z,z) = OccupationKernelRow.pairing Γ z z` read as a real number (it is
finite, `pairing_bridge`). -/
theorem score_tendsto (hΓloc : IsLocallyFiniteMeasure Γ) :
    Tendsto (fun n => integratedRate a Γ (ctrl a n z) - rawCost a Γ (ctrl a n z) / 2) atTop
      (𝓝 (lamZ Γ z 1 - TemporalEquilibrium.mass a / 2 *
        (OccupationKernelRow.pairing Γ (zE z) (zE z)).toReal)) := by
  obtain ⟨-, -, -, hB, -⟩ := pairing_bridge hΓt hμt hsp hΓloc hz hz0
  have hc : Tendsto (fun n => rawCost a Γ (ctrl a n z)) atTop
      (𝓝 (TemporalEquilibrium.mass a * ∫ x, z x * conv Γ z x)) := by
    simp only [rawCost_ctrl]
    exact (fnkn_tendsto ha0 ha1).mul_const _
  rw [hB]
  have := (integratedRate_tendsto hΓt hμt hsp ha0 ha1 hz hz0).sub (hc.div_const 2)
  convert this using 2
  ring

/-- `E:spatial-static-score` (TeX lines 50-53) in the existential form (Le's
decision 2 of wave L6): for every `y < λ_z(1) - (M_a/2) B_Γ(z,z)` there is a
control `Ψ ∈ C_pos` with `y < I_Ψ - v_Ψ/2`, whose rate and cost integrands are
integrable (so its score is not a junk value).  `B_Γ(z,z)` is finite.  General
form: tempered locally finite `Γ`, tempered `μ`, spectral convention,
`0 < a < 1`; neither `Γ ≠ 0` nor the floor is needed. -/
theorem static_score (hzne : z ≠ 0) (hΓloc : IsLocallyFiniteMeasure Γ) :
    OccupationKernelRow.pairing Γ (zE z) (zE z) ≠ ⊤ ∧
    ∀ y : ℝ, y < lamZ Γ z 1 - TemporalEquilibrium.mass a / 2 *
        (OccupationKernelRow.pairing Γ (zE z) (zE z)).toReal →
      ∃ Ψ ∈ CPos d, y < integratedRate a Γ Ψ - rawCost a Γ Ψ / 2 ∧
        IntegrableOn (rate a Γ Ψ) (Ioo 0 1) ∧
        IntegrableOn (fun σ => ∫ x, Ψ (σ, x) * mean a Γ Ψ σ x) (Ioo 0 1) := by
  refine ⟨(pairing_bridge hΓt hμt hsp hΓloc hz hz0).2.2.1, fun y hy => ?_⟩
  have hev := (score_tendsto hΓt hμt hsp ha0 ha1 hz hz0 hΓloc).eventually (lt_mem_nhds hy)
  obtain ⟨n, hn⟩ := hev.exists
  have hg := ctrl_genuine hΓt hμt hsp ha0 ha1 hz hz0 n
  exact ⟨ctrl a n z, ctrl_mem ha0 ha1 n hz hz0 hzne, hn, hg.2.1, hg.2.2.2⟩

end score

/-! ### Constant potentials and satisfiability of the floor -/

/-- Auxiliary to the Lean proof route.  The `L²` dilation of a unit pair is a
unit pair, and `‖∇(U_r f)‖₂² = r² ‖∇f‖₂²` (from `WeakSobolev.IsRayleighTrial.dil`
at the zero potential). -/
theorem isUnitH1_dil {f : Rd d → ℝ} {g : Rd d → Rd d} (h : IsUnitH1 f g) {r : ℝ}
    (hr : 0 < r) :
    IsUnitH1 (WeakSobolev.dilL2 r f) (fun x => r • WeakSobolev.dilL2 r g x) ∧
      ∫ x, ‖r • WeakSobolev.dilL2 r g x‖ ^ 2 = r ^ 2 * ∫ x, ‖g x‖ ^ 2 := by
  have hT : IsRayleighTrial (fun _ : Rd d => (0 : ℝ)) f g :=
    (isRayleighTrial_iff_of_bounded continuous_const (M := 0) (fun _ => by simp) f g).2 h
  obtain ⟨hT', hv⟩ := hT.dil hr
  refine ⟨⟨hT'.memLp_f, hT'.memLp_g, hT'.weakGrad, hT'.unit⟩, ?_⟩
  unfold rayleighValue at hv
  simp only [mul_zero, zero_mul, integral_zero, zero_sub] at hv
  linarith

/-- For a constant potential `K` the real Rayleigh set is nonempty, bounded
above, and its supremum is exactly `K` (spreading unit tests). -/
theorem rayleighSet_const (K : ℝ) :
    (rayleighSet (fun _ : Rd d => K)).Nonempty ∧ BddAbove (rayleighSet (fun _ : Rd d => K)) ∧
      sSup (rayleighSet (fun _ : Rd d => K)) = K := by
  have hb : ∀ x : Rd d, |(fun _ : Rd d => K) x| ≤ |K| := fun _ => le_rfl
  have hne := rayleighSet_nonempty_of_bounded (d := d) continuous_const hb
  have hbdd : BddAbove (rayleighSet (fun _ : Rd d => K)) :=
    rayleighSet_bddAbove (M := K) fun _ => le_rfl
  have hval : ∀ {f : Rd d → ℝ} {g : Rd d → Rd d}, IsUnitH1 f g →
      rayleighValue (fun _ : Rd d => K) f g = K - ∫ x, ‖g x‖ ^ 2 := by
    intro f g h
    unfold rayleighValue
    rw [integral_const_mul, h.2.2.2, mul_one]
  refine ⟨hne, hbdd, le_antisymm (csSup_le hne fun q hq => ?_) (le_of_forall_lt fun y hy => ?_)⟩
  · obtain ⟨f, g, h, rfl⟩ := hq
    exact rayleighValue_le (fun _ => le_rfl) h
  · obtain ⟨f, g, h⟩ := exists_isUnitH1 (d := d)
    set B := ∫ x, ‖g x‖ ^ 2 with hBdef
    have hB : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
    set r := Real.sqrt ((K - y) / (2 * (B + 1))) with hrdef
    have hr2 : r ^ 2 = (K - y) / (2 * (B + 1)) := Real.sq_sqrt (by
      have : 0 < K - y := by linarith
      positivity)
    have hr : 0 < r := Real.sqrt_pos.2 (by
      have : 0 < K - y := by linarith
      positivity)
    obtain ⟨hu, hg⟩ := isUnitH1_dil h hr
    have hT := (isRayleighTrial_iff_of_bounded continuous_const hb _ _).2 hu
    refine lt_of_lt_of_le ?_ (le_csSup hbdd ⟨_, _, hT, rfl⟩)
    rw [hval hu, hg, hr2]
    have hKy : 0 < K - y := by linarith
    have : (K - y) / (2 * (B + 1)) * B < K - y := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

/-- `λ_U(c)² = c m` for the constant potential `U = m` (every real `c`, `m`). -/
theorem lamSq_const (m c : ℝ) : lamSq (fun _ : Rd d => m) c = c * m :=
  (rayleighSet_const (d := d) (c * m)).2.2

/-- Satisfiability check of the named input `RayleighFloor`: it holds for the
unrestricted covariance `Γ = Lebesgue measure` (for which `U_z = ∫ z` is a
positive constant).  This `Γ` lies outside `H:homog`: `Γ(cA) = c^d Γ(A)`
corresponds to `α = 0`, outside the range `0 < α`; it is not spatial white
noise, which is `Γ = δ₀`. -/
theorem rayleighFloor_volume : RayleighFloor (volume : Measure (Rd d)) := by
  intro z hz hz0 hzne
  have hU : conv volume z = fun _ => ∫ y, z y := by
    funext x
    exact integral_sub_left_eq_self z volume x
  have hpos : 0 < ∫ y, z y := by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hzne
    exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
      hz.1.continuous hz.2 hz0 hx
  rw [hU]
  obtain ⟨hne, -, hsup⟩ := rayleighSet_const (d := d) (∫ y, z y)
  exact exists_lt_of_lt_csSup hne (hsup.symm ▸ hpos)

/-! ### The manuscript's statements -/

/-- **`L:spatial-static-controls`, part (i)** (TeX lines 40-49, proof 56-64),
with the section's standing hypotheses (TeX lines 4-5: a nonzero covariance
satisfying `H:homog`, `a = α₀`; the potential `U_z = Γ * z` does not depend on
`a`) and the named input `RayleighFloor Γ` (the dilation floor lemma of wave
item L6-d at `V = Γ * z`; it uses `α < 2` and `Γ ≠ 0`).  For every nonnegative
nonzero `z ∈ C_c^∞(ℝ^d)`: each `U_z(x)` is a genuine integral; for `c > 0` the
set of values `c ∫ U_z g² - ‖∇g‖₂²` over unit `g ∈ H^1` is nonempty and bounded
above (finite supremum), `λ_z(c)² > 0`, `λ_z(c) > 0`; and `λ_z` is Lipschitz on
every `[c₁, c₂]` with `c₁ > 0`.  Proof route: finiteness and the Lipschitz
bound as in the TeX (comparison of identical unit tests, the bound of `U_z`
from `VariationalMean.conv_le` instead of `P:variational-unmasked-rate`);
positivity from the named floor input, not through
`P:compact-original-common-trial` as in the TeX (lines 57-62).  `Γ ≠ 0` and the
fields of `H:homog` other than `Γ_tempered`, `μ_tempered`, `spectral` are
carried, unused (they enter through the floor input). -/
theorem spatial_static_controls_rate_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0) (hfloor : RayleighFloor Γ)
    {z : Rd d → ℝ} (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) :
    (∀ x, Integrable (fun y => z (x - y)) Γ) ∧
    (∀ c : ℝ, 0 < c → (rayleighSet (fun x => c * conv Γ z x)).Nonempty ∧
      BddAbove (rayleighSet (fun x => c * conv Γ z x)) ∧
      0 < lamSq (conv Γ z) c ∧ 0 < lamZ Γ z c ∧ lamZ Γ z c ^ 2 = lamSq (conv Γ z) c) ∧
    (∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ K : NNReal, LipschitzOnWith K (lamZ Γ z) (Icc c₁ c₂)) := by
  obtain ⟨h1, h2, -, -, h5⟩ :=
    static_rate hH.Γ_tempered hH.μ_tempered hH.spectral hfloor hz hz0 hzne
  exact ⟨(convZ_props hH.Γ_tempered hH.μ_tempered hH.spectral hz hz0).1,
    fun c hc => ⟨(h1 c).1, (h1 c).2, h2 c hc⟩, h5⟩

/-- **`L:spatial-static-controls`, part (ii)**, `E:spatial-static-score` (TeX
lines 50-53, proof 66-95) in the existential form (Le's decision 2 of wave L6),
with the section's standing hypotheses (`H:homog`, `Γ ≠ 0`, `a = α₀`): for every
nonnegative nonzero `z ∈ C_c^∞(ℝ^d)`, `B_Γ(z,z)` (`OccupationKernelRow.pairing`,
`E:spatial-physical-pair`) is finite, the Rayleigh set defining `λ_z(1)` is
nonempty and bounded above, and every `y < λ_z(1) - (M_a/2) B_Γ(z,z)` is
exceeded by the score `I_Ψ - v_Ψ/2` of some `Ψ ∈ C_pos` whose rate and cost
integrands are integrable.  This is equivalent to the TeX display whenever
`S_1^pos` is a finite supremum; the sSup form is
`spatial_static_score_sSup_paper`, on the named input `S1Bdd`.  `I_Ψ` is the
integral of `λ_{Ψ,s}` defined by the real Rayleigh form
(`VariationalDilation.rate`) and `v_Ψ` the integral form of the cost
(`VariationalDilation.rawCost`); their identification with `√(-E_s)` and
`E W(Ψ)²` is outside Lean (`P:variational-unmasked-rate`,
`L:compact-raw-profile`).  Neither the floor nor `Γ ≠ 0` is used (`Γ ≠ 0` is
carried); the cutoff `f_n` differs from the TeX's (see `cut`). -/
theorem spatial_static_score_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0)
    {z : Rd d → ℝ} (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) :
    OccupationKernelRow.pairing Γ (zE z) (zE z) ≠ ⊤ ∧
    (rayleighSet (fun x => 1 * conv Γ z x)).Nonempty ∧
    BddAbove (rayleighSet (fun x => 1 * conv Γ z x)) ∧
    ∀ y : ℝ, y < lamZ Γ z 1 - TemporalEquilibrium.mass alpha0 / 2 *
        (OccupationKernelRow.pairing Γ (zE z) (zE z)).toReal →
      ∃ Ψ ∈ CPos d, y < integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 ∧
        IntegrableOn (rate alpha0 Γ Ψ) (Ioo 0 1) ∧
        IntegrableOn (fun σ => ∫ x, Ψ (σ, x) * mean alpha0 Γ Ψ σ x) (Ioo 0 1) := by
  obtain ⟨-, hUc, hU0, M, hUM⟩ := convZ_props hH.Γ_tempered hH.μ_tempered hH.spectral hz hz0
  obtain ⟨h1, h2⟩ := static_score hH.Γ_tempered hH.μ_tempered hH.spectral hH.alpha0_pos
    hH.alpha0_lt_one hz hz0 hzne hH.Γ_radon
  exact ⟨h1, cU_nonempty hUc hU0 hUM 1, cU_bddAbove hU0 hUM 1, h2⟩

/-- The sSup form of `E:spatial-static-score` on the named input `S1Bdd`
(TeX lines 50-53 read with `S_1^pos` the finite supremum of
`P:variational-positive-scores`, TeX lines 272-274 of
`integrated_unmasked_variational.tex`): under the same hypotheses as
`spatial_static_score_paper` and `S1Bdd α₀ Γ`,
`S_1^pos ≥ λ_z(1) - (M_a/2) B_Γ(z,z)`.  Narrower than the TeX only in that the
finiteness of `S_1^pos` is the named input `S1Bdd` (the TeX takes it from
`P:variational-positive-scores`). -/
theorem spatial_static_score_sSup_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hS : S1Bdd (d := d) alpha0 Γ)
    {z : Rd d → ℝ} (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) :
    lamZ Γ z 1 - TemporalEquilibrium.mass alpha0 / 2 *
        (OccupationKernelRow.pairing Γ (zE z) (zE z)).toReal ≤ S1pos alpha0 Γ := by
  obtain ⟨-, -, -, h⟩ := spatial_static_score_paper hH hΓ0 hz hz0 hzne
  refine le_of_forall_lt fun y hy => ?_
  obtain ⟨Ψ, hΨ, hy', -⟩ := h y hy
  exact lt_of_lt_of_le hy' (le_csSup hS ⟨Ψ, hΨ, rfl⟩)

end StratonovichHAMSecondMoment.SpatialStaticControls
