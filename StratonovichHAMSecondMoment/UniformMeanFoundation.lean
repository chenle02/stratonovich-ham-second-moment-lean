module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L15, item L15-UM, UM-0 (agent A; scope (a), approved by Le on 2026-11-19): the shared
foundation lemmas on `H^{±1/2}`, the duality, multipliers and `B_E` that UM-1
(`L:uniform-E-lift`) and UM-2 (`E:positive-raw-mean`) use.  The objects are those of the frozen
interface `StratonovichHAMSecondMoment.UniformMeanInterface` (commit 06c3c6a); nothing there is
changed.

TeX anchors (revision 0788ddee, book 1.1.0, read with `git show 0788ddee:notes/...`; the same
line numbers at edf7085f, book 1.1.3):
* `notes/integrated_compact_gaussian.tex` lines 275-277 (the `H^r` norm `‖⟨ζ⟩^r ũ‖₂`);
* `notes/integrated_cameron_mean.tex` line 6 (`Λ = (1-Δ)^{1/2}`), lines 133-134 (the velocity
  pairing with weight `Λ⁻¹`);
* `notes/integrated_intrinsic_constant.tex` lines 10-11 (`B_E(V)(u,v) = (0,Vu)`), line 36
  (`B_E(m_R h_{Ψ,s})`);
* `notes/integrated_uniform_products.tex` lines 29-31 (`V_q`, `M_q`, `L_q^E`) and 48-69 (proof
  of `L:uniform-E-lift`: density of tests, `M u = V u` on tests, the norm equality).

Main results (the UM-0 list of `docs/l15/INTERFACE.md`, section 3, with the frozen signatures):
`denseRange_toHhalf`, `denseRange_toHmhalf`, `dpair_toHmhalf_toHhalf`, `inner_toHmhalf_lam`,
`toHhalf_add`, `toHhalf_smul`, `toHmhalf_add`, `toHmhalf_smul`, `IsMultiplier.unique`,
`exists_isMultiplier`, `norm_BE`, `BE_injective`, `BE_apply`; also `BE_sub`, `isometry_BE`.

Lean proof route for the density (the one analytic item; the TeX uses density of tests without
proof): a Hermitian `L²` class `U` is approximated by a complex Schwartz `ψ₀`
(`SchwartzMap.denseRange_toLpCLM`); `ψ₀ = ⟨2πξ⟩^σ 𝓕χ` for the Schwartz
`χ = 𝓕⁻(⟨2πξ⟩^{-σ} ψ₀)`; `χ_n Re χ` and `χ_n Im χ` are real tests (`χ_n` the cutoff of
`H1Density`), and for `σ ≤ 1` the coordinate error is bounded by the `H¹` energy
`‖h‖₂² + Σ_j ‖∂_j h‖₂²` of `h = χ_n χ - χ` (Plancherel and `𝓕 ∂_j = 2πi ξ_j 𝓕`), which tends
to zero.  Finally the imaginary part is dropped: for Hermitian `X, Y`,
`‖X‖ ≤ ‖X + iY‖` because the complex pairing of Hermitian classes is real.

No `sorry`, no axiom; every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.UniformMeanInterface
public import StratonovichHAMSecondMoment.H1Density

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff SchwartzMap RealInnerProductSpace ComplexConjugate Real LineDeriv

namespace StratonovichHAMSecondMoment.UniformMeanInterface

open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)

variable {d : ℕ}

/-! ### Linearity on tests -/

/-- Auxiliary: real tests are closed under addition. -/
theorem isTest_add {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    IsTestFunction (φ + ψ) := ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩

/-- Auxiliary: real tests are closed under scalar multiplication. -/
theorem isTest_smul (c : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    IsTestFunction (c • φ) :=
  ⟨hφ.1.const_smul c, (hφ.2.mul_left (f := fun _ => c) : HasCompactSupport fun x => c * φ x)⟩

/-- Auxiliary: the product of two real tests is a test. -/
theorem isTest_mul {u φ : Rd d → ℝ} (hu : IsTestFunction u) (hφ : IsTestFunction φ) :
    IsTestFunction fun x => u x * φ x := ⟨hu.1.mul hφ.1, hφ.2.mul_left⟩

/-- Auxiliary: a smooth function times a real test is a test. -/
theorem isTest_smooth_mul {V φ : Rd d → ℝ} (hV : ContDiff ℝ ∞ V) (hφ : IsTestFunction φ) :
    IsTestFunction fun x => V x * φ x := ⟨hV.mul hφ.1, hφ.2.mul_left⟩

/-- Auxiliary: `toLp` is additive on Schwartz functions. -/
theorem schwartz_toLp_add (f g : 𝓢(Rd d, ℂ)) :
    (f + g).toLp 2 (volume : Measure (Rd d)) =
      f.toLp 2 (volume : Measure (Rd d)) + g.toLp 2 (volume : Measure (Rd d)) := by
  refine Lp.ext ?_
  filter_upwards [(f + g).coeFn_toLp 2 (volume : Measure (Rd d)),
    f.coeFn_toLp 2 (volume : Measure (Rd d)), g.coeFn_toLp 2 (volume : Measure (Rd d)),
    Lp.coeFn_add (f.toLp 2 (volume : Measure (Rd d))) (g.toLp 2 (volume : Measure (Rd d)))]
    with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]; rfl

/-- Auxiliary: `toLp` commutes with complex scalars on Schwartz functions. -/
theorem schwartz_toLp_smul (c : ℂ) (f : 𝓢(Rd d, ℂ)) :
    (c • f).toLp 2 (volume : Measure (Rd d)) = c • f.toLp 2 (volume : Measure (Rd d)) := by
  refine Lp.ext ?_
  filter_upwards [(c • f).coeFn_toLp 2 (volume : Measure (Rd d)),
    f.coeFn_toLp 2 (volume : Measure (Rd d)),
    Lp.coeFn_smul c (f.toLp 2 (volume : Measure (Rd d)))] with x h1 h2 h4
  rw [h1, h4, Pi.smul_apply, h2]; rfl

/-- Auxiliary: `testSchwartz` is additive. -/
theorem testSchwartz_add {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ)
    (h : IsTestFunction (φ + ψ)) :
    H1Mathlib.testSchwartz h = H1Mathlib.testSchwartz hφ + H1Mathlib.testSchwartz hψ := by
  ext x; simp

/-- Auxiliary: `testSchwartz` commutes with real scalars. -/
theorem testSchwartz_smul (c : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ)
    (h : IsTestFunction (c • φ)) :
    H1Mathlib.testSchwartz h = (c : ℂ) • H1Mathlib.testSchwartz hφ := by
  ext x; simp

/-- Auxiliary: the Schwartz coordinate is additive. -/
theorem coordSchwartz_add (σ : ℝ) {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ)
    (hψ : IsTestFunction ψ) (h : IsTestFunction (φ + ψ)) :
    coordSchwartz σ h = coordSchwartz σ hφ + coordSchwartz σ hψ := by
  rw [coordSchwartz, coordSchwartz, coordSchwartz, testSchwartz_add hφ hψ h, FourierAdd.fourier_add,
    map_add]

/-- Auxiliary: the Schwartz coordinate commutes with real scalars. -/
theorem coordSchwartz_smul (σ c : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ)
    (h : IsTestFunction (c • φ)) :
    coordSchwartz σ h = (c : ℂ) • coordSchwartz σ hφ := by
  rw [coordSchwartz, coordSchwartz, testSchwartz_smul c hφ h, FourierSMul.fourier_smul, map_smul]

/-- Auxiliary: the `L²` coordinate is additive on tests. -/
theorem coord_add (σ : ℝ) {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    coord σ (φ + ψ) = coord σ φ + coord σ ψ := by
  have h := isTest_add hφ hψ
  simp only [coord, h, hφ, hψ, dite_true]
  rw [coordSchwartz_add σ hφ hψ h, schwartz_toLp_add]

/-- Auxiliary: the `L²` coordinate commutes with real scalars on tests. -/
theorem coord_smul (σ c : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    coord σ (c • φ) = (c : ℂ) • coord σ φ := by
  have h := isTest_smul c hφ
  simp only [coord, h, hφ, dite_true]
  rw [coordSchwartz_smul σ c hφ h, schwartz_toLp_smul]

/-- **Linearity of `φ ↦ [φ]_{H^{1/2}}` on tests** (additivity). -/
theorem toHhalf_add {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    toHhalf (φ + ψ) = toHhalf φ + toHhalf ψ := by
  apply Subtype.ext
  change ((show HR d from toHhalf (φ + ψ)) : Lp ℂ 2 (volume : Measure (Rd d))) =
    ((show HR d from toHhalf φ) : Lp ℂ 2 (volume : Measure (Rd d))) +
      ((show HR d from toHhalf ψ) : Lp ℂ 2 (volume : Measure (Rd d)))
  rw [toHhalf_coe (isTest_add hφ hψ), toHhalf_coe hφ, toHhalf_coe hψ, coord_add _ hφ hψ]

/-- **Linearity of `φ ↦ [φ]_{H^{1/2}}` on tests** (homogeneity). -/
theorem toHhalf_smul (c : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    toHhalf (c • φ) = c • toHhalf φ := by
  apply Subtype.ext
  change ((show HR d from toHhalf (c • φ)) : Lp ℂ 2 (volume : Measure (Rd d))) =
    c • ((show HR d from toHhalf φ) : Lp ℂ 2 (volume : Measure (Rd d)))
  rw [toHhalf_coe (isTest_smul c hφ), toHhalf_coe hφ, coord_smul _ _ hφ]; rfl

/-- Auxiliary: the coordinate of a test is `⟨2πξ⟩^σ 𝓕φ(ξ)` almost everywhere. -/
theorem coeFn_coord (σ : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    (coord σ φ : Rd d → ℂ) =ᵐ[volume]
      fun ξ => msWeight σ ξ * 𝓕 (H1Mathlib.testSchwartz hφ) ξ := by
  simp only [coord, hφ, dite_true]
  filter_upwards [(coordSchwartz σ hφ).coeFn_toLp 2 (volume : Measure (Rd d))] with ξ h
  rw [h, coordSchwartz, SchwartzMap.smulLeftCLM_apply_apply (msWeight_growth σ), smul_eq_mul]


/-- Auxiliary: the real inner product of `L²(ℝ^d; ℂ)` is `∫ Re (V conj U)`. -/
theorem real_inner_Lp (U V : Lp ℂ 2 (volume : Measure (Rd d))) :
    ⟪U, V⟫ = ∫ ξ, (V ξ * conj (U ξ)).re := by
  rw [L2.inner_def]; simp only [Complex.inner]

/-- Auxiliary: `⟨2πξ⟩^σ ⟨2πξ⟩^{-σ} = 1`. -/
theorem msWeight_mul_neg (σ : ℝ) (ξ : Rd d) : msWeight σ ξ * msWeight (-σ) ξ = 1 := by
  have hpos : 0 < 1 + ‖(2 * π) • ξ‖ ^ 2 := by positivity
  simp only [msWeight, ← Complex.ofReal_mul, ← Real.rpow_add hpos]
  rw [show σ / 2 + -σ / 2 = 0 by ring, Real.rpow_zero, Complex.ofReal_one]

/-- Auxiliary: the weight is real. -/
theorem conj_msWeight (σ : ℝ) (ξ : Rd d) : conj (msWeight σ ξ) = msWeight σ ξ := by
  simp [msWeight, Complex.conj_ofReal]

/-- Auxiliary: `|⟨2πξ⟩^σ|² = (1 + 4π²|ξ|²)^σ`. -/
theorem norm_msWeight_sq (σ : ℝ) (ξ : Rd d) :
    ‖msWeight σ ξ‖ ^ 2 = (1 + ‖(2 * π) • ξ‖ ^ 2) ^ σ := by
  have hpos : 0 < 1 + ‖(2 * π) • ξ‖ ^ 2 := by positivity
  rw [msWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Real.rpow_natCast,
    ← Real.rpow_mul hpos.le]
  norm_num

/-- Auxiliary: `‖coord σ φ‖² = ∫ (1 + 4π²|ξ|²)^σ |𝓕φ|²` (the manuscript's `H^σ` norm squared). -/
theorem norm_coord_sq (σ : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ‖coord σ φ‖ ^ 2 =
      ∫ ξ, (1 + ‖(2 * π) • ξ‖ ^ 2) ^ σ * ‖𝓕 (H1Mathlib.testSchwartz hφ) ξ‖ ^ 2 := by
  rw [H1Mathlib.norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_coord σ hφ] with ξ h
  rw [h, norm_mul, mul_pow, norm_msWeight_sq]

/-- Auxiliary: the `H^{1/2}` norm of a test is the norm of its coordinate. -/
theorem norm_toHhalf (φ : Rd d → ℝ) (hφ : IsTestFunction φ) :
    ‖toHhalf φ‖ = ‖coord (1 / 2) φ‖ := by
  rw [← toHhalf_coe hφ]; rfl

/-- Auxiliary: the `H^{-1/2}` norm of a test is the norm of its coordinate. -/
theorem norm_toHmhalf (φ : Rd d → ℝ) (hφ : IsTestFunction φ) :
    ‖toHmhalf φ‖ = ‖coord (-1 / 2) φ‖ := by
  rw [← toHmhalf_coe hφ]; rfl

/-- Auxiliary: the real inner product of two coordinates of order `-σ` and `σ` is `∫ v u`
(Plancherel). -/
theorem inner_coord_neg (σ : ℝ) {v u : Rd d → ℝ} (hv : IsTestFunction v)
    (hu : IsTestFunction u) :
    ⟪coord (-σ) v, coord σ u⟫ = ∫ x, v x * u x := by
  have hint : Integrable (fun ξ => inner ℂ (𝓕 (H1Mathlib.testSchwartz hv) ξ)
      (𝓕 (H1Mathlib.testSchwartz hu) ξ)) volume := by
    refine (L2.integrable_inner (𝕜 := ℂ)
      ((𝓕 (H1Mathlib.testSchwartz hv)).toLp 2 (volume : Measure (Rd d)))
      ((𝓕 (H1Mathlib.testSchwartz hu)).toLp 2 (volume : Measure (Rd d)))).congr ?_
    filter_upwards [(𝓕 (H1Mathlib.testSchwartz hv)).coeFn_toLp 2 (volume : Measure (Rd d)),
      (𝓕 (H1Mathlib.testSchwartz hu)).coeFn_toLp 2 (volume : Measure (Rd d))] with ξ h1 h2
    rw [h1, h2]
  have hP : ∫ ξ, inner ℂ (𝓕 (H1Mathlib.testSchwartz hv) ξ) (𝓕 (H1Mathlib.testSchwartz hu) ξ) =
      ((∫ x, v x * u x : ℝ) : ℂ) := by
    rw [SchwartzMap.integral_inner_fourier_fourier]
    have e : ∀ x, inner ℂ (H1Mathlib.testSchwartz hv x) (H1Mathlib.testSchwartz hu x) =
        ((v x * u x : ℝ) : ℂ) := by
      intro x; simp [RCLike.inner_apply]; ring
    simp_rw [e]
    exact integral_complex_ofReal
  rw [real_inner_Lp]
  calc ∫ ξ, ((coord σ u : Rd d → ℂ) ξ * conj ((coord (-σ) v : Rd d → ℂ) ξ)).re
      = ∫ ξ, RCLike.re (inner ℂ (𝓕 (H1Mathlib.testSchwartz hv) ξ)
          (𝓕 (H1Mathlib.testSchwartz hu) ξ)) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_coord σ hu, coeFn_coord (-σ) hv] with ξ h1 h2
        rw [h1, h2, RCLike.inner_apply, map_mul, conj_msWeight]
        change _ = Complex.re _
        congr 1
        linear_combination (conj (𝓕 (H1Mathlib.testSchwartz hv) ξ) *
          𝓕 (H1Mathlib.testSchwartz hu) ξ) * msWeight_mul_neg σ ξ
    _ = RCLike.re (∫ ξ, inner ℂ (𝓕 (H1Mathlib.testSchwartz hv) ξ)
          (𝓕 (H1Mathlib.testSchwartz hu) ξ)) := integral_re hint
    _ = _ := by rw [hP]; simp

/-- **The duality on tests is the `L²` pairing**: `⟨v, u⟩_{H^{-1/2},H^{1/2}} = ∫ v u` for real tests
(Plancherel; the duality of `integrated_cameron_mean.tex` lines 6 and 133-134 at revision edf7085f
(book 1.1.3)). -/
theorem dpair_toHmhalf_toHhalf {v u : Rd d → ℝ} (hv : IsTestFunction v) (hu : IsTestFunction u) :
    dpair (toHmhalf v) (toHhalf u) = ∫ x, v x * u x := by
  have h := inner_coord_neg (1 / 2) hv hu
  rw [show -(1 / 2 : ℝ) = -1 / 2 by norm_num, ← toHmhalf_coe hv, ← toHhalf_coe hu] at h
  rw [← h]; rfl

/-- **The velocity pairing with weight `Λ⁻¹`**: `⟪v, Λ g⟫_{H^{-1/2}} = ∫ v g` for real tests
(`integrated_cameron_mean.tex` lines 133-134 at revision edf7085f (book 1.1.3)). -/
theorem inner_toHmhalf_lam {v g : Rd d → ℝ} (hv : IsTestFunction v) (hg : IsTestFunction g) :
    ⟪toHmhalf v, lam (toHhalf g)⟫ = ∫ x, v x * g x := by
  rw [← dpair_toHmhalf_toHhalf hv hg]; rfl


/-! ### Hermitian classes -/

/-- Auxiliary: membership in `herm d`. -/
theorem mem_herm_iff {X : Lp ℂ 2 (volume : Measure (Rd d))} :
    X ∈ herm d ↔ ∀ᵐ ξ, (X : Rd d → ℂ) (-ξ) = conj ((X : Rd d → ℂ) ξ) := Iff.rfl

/-- Auxiliary: the coordinate of a real test is Hermitian. -/
theorem coord_mem_herm (σ : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : coord σ φ ∈ herm d := by
  have h0 := (coordSchwartz σ hφ).coeFn_toLp 2 (volume : Measure (Rd d))
  rw [mem_herm_iff]
  simp only [coord, hφ, dite_true]
  filter_upwards [h0, ae_comp_neg h0] with ξ h1 h2
  rw [h1, h2, coordSchwartz_neg]

/-- Auxiliary: for Hermitian classes `X, Y`, `∫ Im (Y conj X) = 0` (the complex pairing is real). -/
theorem herm_integral_im {X Y : Lp ℂ 2 (volume : Measure (Rd d))} (hX : X ∈ herm d)
    (hY : Y ∈ herm d) : ∫ ξ, ((Y : Rd d → ℂ) ξ * conj ((X : Rd d → ℂ) ξ)).im = 0 := by
  have hneg : (fun ξ => ((Y : Rd d → ℂ) (-ξ) * conj ((X : Rd d → ℂ) (-ξ))).im) =ᵐ[volume]
      fun ξ => -((Y : Rd d → ℂ) ξ * conj ((X : Rd d → ℂ) ξ)).im := by
    filter_upwards [(mem_herm_iff.mp hX), (mem_herm_iff.mp hY)] with ξ h1 h2
    rw [h1, h2, Complex.conj_conj, show conj ((Y : Rd d → ℂ) ξ) * (X : Rd d → ℂ) ξ =
      conj ((Y : Rd d → ℂ) ξ * conj ((X : Rd d → ℂ) ξ)) by simp, Complex.conj_im]
  have h1 := integral_neg_eq_self
    (fun ξ => ((Y : Rd d → ℂ) ξ * conj ((X : Rd d → ℂ) ξ)).im) (volume : Measure (Rd d))
  rw [integral_congr_ae hneg, integral_neg] at h1
  linarith

/-- Auxiliary: for Hermitian classes, `‖X‖ ≤ ‖X + i Y‖` (`X` and `iY` are real-orthogonal). -/
theorem herm_norm_le {X Y : Lp ℂ 2 (volume : Measure (Rd d))} (hX : X ∈ herm d)
    (hY : Y ∈ herm d) : ‖X‖ ≤ ‖X + Complex.I • Y‖ := by
  have hin : ⟪X, Complex.I • Y⟫ = 0 := by
    rw [real_inner_Lp]
    have e : (fun ξ => (((Complex.I • Y : Lp ℂ 2 (volume : Measure (Rd d))) : Rd d → ℂ) ξ *
        conj ((X : Rd d → ℂ) ξ)).re) =ᵐ[volume]
        fun ξ => -((Y : Rd d → ℂ) ξ * conj ((X : Rd d → ℂ) ξ)).im := by
      filter_upwards [Lp.coeFn_smul Complex.I Y] with ξ h
      rw [h, Pi.smul_apply, smul_eq_mul, mul_assoc, Complex.I_mul_re]
    rw [integral_congr_ae e, integral_neg, herm_integral_im hX hY, neg_zero]
  have h := norm_add_sq_real X (Complex.I • Y)
  rw [hin, mul_zero, add_zero] at h
  have h2 : ‖X‖ ^ 2 ≤ ‖X + Complex.I • Y‖ ^ 2 := by rw [h]; nlinarith [norm_nonneg (Complex.I • Y)]
  nlinarith [norm_nonneg X, norm_nonneg (X + Complex.I • Y)]

/-! ### The weighted Plancherel bound for Schwartz functions -/

/-- Auxiliary: `|f|²` is integrable for a Schwartz `f`. -/
theorem integrable_norm_sq_schwartz (f : 𝓢(Rd d, ℂ)) :
    Integrable (fun x => ‖f x‖ ^ 2) (volume : Measure (Rd d)) := by
  refine (H1Mathlib.integrable_norm_sq (f.toLp 2 (volume : Measure (Rd d)))).congr ?_
  filter_upwards [f.coeFn_toLp 2 (volume : Measure (Rd d))] with x h
  rw [h]

/-- Auxiliary: `|𝓕(∂_j h)|² = 4π² ξ_j² |𝓕h|²`. -/
theorem norm_fourier_lineDeriv_sq (h : 𝓢(Rd d, ℂ)) (j : Fin d) (ξ : Rd d) :
    ‖𝓕 (∂_{H1Mathlib.eb d j} h) ξ‖ ^ 2 =
      (2 * π) ^ 2 * inner ℝ ξ (H1Mathlib.eb d j) ^ 2 * ‖𝓕 h ξ‖ ^ 2 := by
  have hg : (inner ℝ · (H1Mathlib.eb d j) : Rd d → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip (H1Mathlib.eb d j)).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, norm_smul, norm_smul, mul_pow, mul_pow]
  simp [Complex.norm_I, abs_of_pos Real.pi_pos, sq_abs]
  ring

/-- Auxiliary: pointwise `|⟨2πξ⟩^σ 𝓕h|² ≤ |𝓕h|² + Σ_j |𝓕 ∂_j h|²` for `σ ≤ 1`. -/
theorem weighted_le (σ : ℝ) (hσ : σ ≤ 1) (h : 𝓢(Rd d, ℂ)) (ξ : Rd d) :
    ‖msWeight σ ξ * 𝓕 h ξ‖ ^ 2 ≤
      ‖𝓕 h ξ‖ ^ 2 + ∑ j : Fin d, ‖𝓕 (∂_{H1Mathlib.eb d j} h) ξ‖ ^ 2 := by
  have hs : ∑ j : Fin d, ‖𝓕 (∂_{H1Mathlib.eb d j} h) ξ‖ ^ 2 =
      ‖(2 * π) • ξ‖ ^ 2 * ‖𝓕 h ξ‖ ^ 2 := by
    simp_rw [norm_fourier_lineDeriv_sq]
    rw [← Finset.sum_mul, ← Finset.mul_sum, H1Mathlib.sum_sq_coord, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    ring
  rw [hs, norm_mul, mul_pow, norm_msWeight_sq]
  have h1 : (1 + ‖(2 * π) • ξ‖ ^ 2) ^ σ ≤ 1 + ‖(2 * π) • ξ‖ ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 1 + ‖(2 * π) • ξ‖ ^ 2 by nlinarith [norm_nonneg ((2 * π) • ξ)]) hσ
    simpa using this
  nlinarith [sq_nonneg ‖𝓕 h ξ‖]

/-- Auxiliary: `‖⟨2πξ⟩^σ 𝓕h‖₂² ≤ ‖h‖₂² + Σ_j ‖∂_j h‖₂²` for a Schwartz `h` and `σ ≤ 1` (Plancherel).
-/
theorem integral_weighted_le (σ : ℝ) (hσ : σ ≤ 1) (h : 𝓢(Rd d, ℂ)) :
    ∫ ξ, ‖msWeight σ ξ * 𝓕 h ξ‖ ^ 2 ≤
      (∫ x, ‖h x‖ ^ 2) + ∑ j : Fin d, ∫ x, ‖(∂_{H1Mathlib.eb d j} h) x‖ ^ 2 := by
  have hL : Integrable (fun ξ => ‖msWeight σ ξ * 𝓕 h ξ‖ ^ 2) (volume : Measure (Rd d)) := by
    refine (integrable_norm_sq_schwartz (SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 h))).congr
      (Eventually.of_forall fun ξ => ?_)
    simp only [SchwartzMap.smulLeftCLM_apply_apply (msWeight_growth σ), smul_eq_mul]
  have hR : ∀ j ∈ Finset.univ, Integrable (fun ξ => ‖𝓕 (∂_{H1Mathlib.eb d j} h) ξ‖ ^ 2)
      (volume : Measure (Rd d)) := fun j _ => integrable_norm_sq_schwartz _
  calc ∫ ξ, ‖msWeight σ ξ * 𝓕 h ξ‖ ^ 2
      ≤ ∫ ξ, (‖𝓕 h ξ‖ ^ 2 + ∑ j : Fin d, ‖𝓕 (∂_{H1Mathlib.eb d j} h) ξ‖ ^ 2) :=
        integral_mono hL ((integrable_norm_sq_schwartz _).add (integrable_finsetSum _ hR))
          (fun ξ => weighted_le σ hσ h ξ)
    _ = _ := by
        rw [integral_add (integrable_norm_sq_schwartz _) (integrable_finsetSum _ hR),
          integral_finsetSum _ hR, SchwartzMap.integral_norm_sq_fourier]
        simp only [SchwartzMap.integral_norm_sq_fourier]


/-! ### Cutting off a Schwartz function -/

open H1Density (cutoff cutoff_contDiff cutoff_isTest) in
/-- The real test `χ_n Re ψ` (`χ_n` the cutoff of `H1Density`). -/
def cutRe (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) (x : Rd d) : ℝ := cutoff n x * (ψ x).re

open H1Density (cutoff cutoff_contDiff cutoff_isTest) in
/-- The real test `χ_n Im ψ`. -/
def cutIm (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) (x : Rd d) : ℝ := cutoff n x * (ψ x).im

/-- Auxiliary: `χ_n Re ψ` is a real test. -/
theorem cutRe_isTest (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) : IsTestFunction (cutRe ψ n) :=
  H1Density.cutoff_isTest n (Complex.reCLM.contDiff.comp (ψ.smooth ⊤))

/-- Auxiliary: `χ_n Im ψ` is a real test. -/
theorem cutIm_isTest (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) : IsTestFunction (cutIm ψ n) :=
  H1Density.cutoff_isTest n (Complex.imCLM.contDiff.comp (ψ.smooth ⊤))

/-- The Schwartz error `χ_n ψ - ψ`. -/
def cutErr (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) : 𝓢(Rd d, ℂ) :=
  H1Mathlib.testSchwartz (cutRe_isTest ψ n) +
    Complex.I • H1Mathlib.testSchwartz (cutIm_isTest ψ n) + -ψ

/-- Auxiliary: `cutErr ψ n = χ_n ψ - ψ` pointwise. -/
theorem cutErr_coe (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) :
    (cutErr ψ n : Rd d → ℂ) = fun x => H1Density.cutoff n x • ψ x - ψ x := by
  funext x
  simp only [cutErr, add_apply, smul_apply, neg_apply,
    H1Mathlib.testSchwartz_apply, cutRe, cutIm, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

/-- Auxiliary: `χ_n ψ → ψ` in `L²`. -/
theorem tendsto_cutErr (ψ : 𝓢(Rd d, ℂ)) :
    Tendsto (fun n => eLpNorm (cutErr ψ n : Rd d → ℂ) 2 volume) atTop (𝓝 0) := by
  simp_rw [cutErr_coe]
  exact H1Density.tendsto_cutoff_smul (ψ.memLp 2 volume)

/-- Auxiliary: the product rule for `∂_e (χ_n ψ - ψ)`. -/
theorem lineDeriv_cutErr (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) (e x : Rd d) :
    (∂_{e} (cutErr ψ n)) x = (H1Density.cutoff n x • (∂_{e} ψ) x - (∂_{e} ψ) x) +
      fderiv ℝ (H1Density.cutoff n) x e • ψ x := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, cutErr_coe, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hc : HasFDerivAt (H1Density.cutoff (d := d) n) (fderiv ℝ (H1Density.cutoff n) x) x :=
    ((H1Density.cutoff_contDiff n).differentiable (by simp) x).hasFDerivAt
  have hψ : HasFDerivAt (ψ : Rd d → ℂ) (fderiv ℝ ψ x) x := ψ.differentiableAt.hasFDerivAt
  have hd : HasFDerivAt (fun y => H1Density.cutoff n y • ψ y - ψ y)
      (H1Density.cutoff n x • fderiv ℝ ψ x +
        (fderiv ℝ (H1Density.cutoff n) x).smulRight (ψ x) - fderiv ℝ ψ x) x :=
    (hc.smul hψ).sub hψ
  rw [hd.fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply]
  abel

/-- Auxiliary: `∂_j (χ_n ψ) → ∂_j ψ` in `L²`. -/
theorem tendsto_lineDeriv_cutErr (ψ : 𝓢(Rd d, ℂ)) (j : Fin d) :
    Tendsto (fun n =>
      eLpNorm ((∂_{H1Mathlib.eb d j} (cutErr ψ n) : 𝓢(Rd d, ℂ)) : Rd d → ℂ) 2 volume)
      atTop (𝓝 0) := by
  set e := H1Mathlib.eb d j
  obtain ⟨C, hC0, hC⟩ := H1Density.exists_bound_fderiv_cutBump (d := d)
  have hA := H1Density.tendsto_cutoff_smul ((∂_{e} ψ).memLp 2 volume)
  have hB : Tendsto (fun n : ℕ => ENNReal.ofReal (C / ((n : ℝ) + 1)) * eLpNorm ψ 2 volume)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [mul_one_div]
    have h1 := ENNReal.tendsto_ofReal h0
    rw [ENNReal.ofReal_zero] at h1
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr (ψ.memLp 2 volume).eLpNorm_lt_top.ne)
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  have hsplit : ((∂_{e} (cutErr ψ n) : 𝓢(Rd d, ℂ)) : Rd d → ℂ) =
      (fun x => H1Density.cutoff n x • (∂_{e} ψ) x - (∂_{e} ψ) x) +
        fun x => fderiv ℝ (H1Density.cutoff n) x e • ψ x := by
    funext x; rw [lineDeriv_cutErr, Pi.add_apply]
  have hcf : Continuous fun x => fderiv ℝ (H1Density.cutoff (d := d) n) x e :=
    ((H1Density.cutoff_contDiff n).continuous_fderiv (by simp)).clm_apply continuous_const
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans (add_le_add le_rfl ?_)
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hcf.smul ψ.continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_) 2
  rw [Pi.smul_apply', norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hg := H1Density.norm_grad_cutoff_le hC n x
  simp only [VariationalFloor.grad, LinearIsometryEquiv.norm_map] at hg
  calc ‖fderiv ℝ (H1Density.cutoff n) x e‖ ≤ ‖fderiv ℝ (H1Density.cutoff n) x‖ * ‖e‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (H1Density.cutoff n) x‖ := by simp [e]
    _ ≤ _ := hg


/-! ### Density of tests -/

/-- Auxiliary: the `L²` norm of `⟨2πξ⟩^σ 𝓕h` as an integral. -/
theorem norm_toLp_smulLeft_sq (σ : ℝ) (h : 𝓢(Rd d, ℂ)) :
    ‖(SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 h)).toLp 2 (volume : Measure (Rd d))‖ ^ 2 =
      ∫ ξ, ‖msWeight σ ξ * 𝓕 h ξ‖ ^ 2 := by
  rw [H1Mathlib.norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [(SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 h)).coeFn_toLp 2
    (volume : Measure (Rd d))] with ξ hξ
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (msWeight_growth σ), smul_eq_mul]

/-- Auxiliary: the `H¹` energy of `χ_n ψ - ψ` tends to zero. -/
theorem tendsto_cutErr_energy (ψ : 𝓢(Rd d, ℂ)) :
    Tendsto (fun n => (∫ x, ‖cutErr ψ n x‖ ^ 2) +
      ∑ j : Fin d, ∫ x, ‖(∂_{H1Mathlib.eb d j} (cutErr ψ n)) x‖ ^ 2) atTop (𝓝 0) := by
  have e1 : ∀ n, ∫ x, ‖cutErr ψ n x‖ ^ 2 =
      (eLpNorm (cutErr ψ n : Rd d → ℂ) 2 volume).toReal ^ 2 := fun n =>
    H1Mathlib.integral_norm_sq_eq ((cutErr ψ n).memLp 2 volume)
  have e2 : ∀ n (j : Fin d), ∫ x, ‖(∂_{H1Mathlib.eb d j} (cutErr ψ n)) x‖ ^ 2 =
      (eLpNorm ((∂_{H1Mathlib.eb d j} (cutErr ψ n) : 𝓢(Rd d, ℂ)) : Rd d → ℂ) 2
        volume).toReal ^ 2 := fun n j =>
    H1Mathlib.integral_norm_sq_eq ((∂_{H1Mathlib.eb d j} (cutErr ψ n)).memLp 2 volume)
  simp_rw [e1, e2]
  have h := (H1Mathlib.tendsto_sq_toReal (tendsto_cutErr ψ)).add
    (tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
      H1Mathlib.tendsto_sq_toReal (tendsto_lineDeriv_cutErr ψ j))
  simpa using h

/-- Auxiliary: `⟨2πξ⟩^σ 𝓕 𝓕⁻(⟨2πξ⟩^{-σ} ψ) = ψ`. -/
theorem smulLeft_fourierInv (σ : ℝ) (ψ : 𝓢(Rd d, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (msWeight σ)
      (𝓕 (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ))) = ψ := by
  ext ξ
  rw [FourierInvPair.fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply (msWeight_growth σ),
    SchwartzMap.smulLeftCLM_apply_apply (msWeight_growth (-σ)), smul_smul, msWeight_mul_neg,
    one_smul]

/-- Auxiliary: the coordinate of the error, in terms of the real and imaginary cut tests. -/
theorem toLp_smulLeft_cutErr (σ : ℝ) (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) :
    (SchwartzMap.smulLeftCLM ℂ (msWeight σ)
      (𝓕 (cutErr (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ)) n))).toLp 2
        (volume : Measure (Rd d)) =
      coord σ (cutRe (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ)) n) +
        Complex.I • coord σ (cutIm (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ)) n) -
          ψ.toLp 2 (volume : Measure (Rd d)) := by
  set χ := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ)
  have ha := cutRe_isTest χ n
  have hb := cutIm_isTest χ n
  simp only [coord, ha, hb, dite_true]
  have e : SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 (cutErr χ n)) =
      coordSchwartz σ ha + Complex.I • coordSchwartz σ hb - ψ := by
    rw [cutErr, FourierAdd.fourier_add, FourierAdd.fourier_add, FourierSMul.fourier_smul,
      FourierTransform.fourier_neg, map_add, map_add, map_smul, map_neg, smulLeft_fourierInv,
      coordSchwartz,
      coordSchwartz, sub_eq_add_neg]
  rw [e]
  change SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Rd d)) _ =
    SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Rd d)) _ +
      Complex.I • SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Rd d)) _ -
        SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Rd d)) _
  rw [map_sub, map_add, map_smul]

/-- Auxiliary: approximation of Hermitian classes by coordinates of real tests (`σ ≤ 1`). -/
theorem exists_test_coord_near_herm (σ : ℝ) (hσ : σ ≤ 1) {U : Lp ℂ 2 (volume : Measure (Rd d))}
    (hU : U ∈ herm d) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ, IsTestFunction φ ∧ ‖coord σ φ - U‖ < ε := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := Rd d) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top
  obtain ⟨ψ, hψ⟩ := (Metric.denseRange_iff.mp hd) U (ε / 2) (by linarith)
  set χ := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ)
  obtain ⟨n, hn⟩ := ((tendsto_cutErr_energy χ).eventually
    (gt_mem_nhds (show (0 : ℝ) < (ε / 2) ^ 2 by positivity))).exists
  have hK : ‖coord σ (cutRe χ n) + Complex.I • coord σ (cutIm χ n) -
      ψ.toLp 2 (volume : Measure (Rd d))‖ < ε / 2 := by
    rw [← toLp_smulLeft_cutErr]
    have h1 := norm_toLp_smulLeft_sq σ (cutErr χ n)
    have h2 := integral_weighted_le σ hσ (cutErr χ n)
    nlinarith [norm_nonneg ((SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 (cutErr χ n))).toLp 2
      (volume : Measure (Rd d)))]
  have hX : coord σ (cutRe χ n) - U ∈ herm d := (herm d).sub_mem (coord_mem_herm σ
    (cutRe_isTest χ n)) hU
  have hψ' : ‖ψ.toLp 2 (volume : Measure (Rd d)) - U‖ < ε / 2 := by
    rw [← dist_eq_norm, dist_comm]; exact hψ
  refine ⟨cutRe χ n, cutRe_isTest χ n, ?_⟩
  calc ‖coord σ (cutRe χ n) - U‖
      ≤ ‖(coord σ (cutRe χ n) - U) + Complex.I • coord σ (cutIm χ n)‖ :=
        herm_norm_le hX (coord_mem_herm σ (cutIm_isTest χ n))
    _ = ‖(coord σ (cutRe χ n) + Complex.I • coord σ (cutIm χ n) -
          ψ.toLp 2 (volume : Measure (Rd d))) + (ψ.toLp 2 (volume : Measure (Rd d)) - U)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hK hψ'
    _ = ε := by ring

/-- Auxiliary: approximation of elements of `HR d` by coordinates of real tests (`σ ≤ 1`). -/
theorem exists_test_coord_near (σ : ℝ) (hσ : σ ≤ 1) {U : Lp ℂ 2 (volume : Measure (Rd d))}
    (hU : U ∈ HR d) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ, IsTestFunction φ ∧ ‖coord σ φ - U‖ < ε := by
  have hc : U ∈ closure (herm d : Set (Lp ℂ 2 (volume : Measure (Rd d)))) := by
    rw [← Submodule.topologicalClosure_coe]; exact hU
  obtain ⟨V, hV, hUV⟩ := Metric.mem_closure_iff.mp hc (ε / 2) (by linarith)
  obtain ⟨φ, hφ, h⟩ := exists_test_coord_near_herm σ hσ hV (half_pos hε)
  refine ⟨φ, hφ, ?_⟩
  rw [dist_eq_norm] at hUV
  calc ‖coord σ φ - U‖ ≤ ‖coord σ φ - V‖ + ‖V - U‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by rw [norm_sub_rev V U]; linarith

/-- **Density of real tests in `H^{1/2}`** (UM-0, the density used throughout
`integrated_uniform_products.tex` lines 55-57 at revision edf7085f (book 1.1.3)): Hermitian `L²`
classes are approximated by coordinates of complex Schwartz functions, whose real parts are cut off
to real tests; the error is controlled by the manuscript `H¹` energy. -/
theorem denseRange_toHhalf :
    Dense {x : Hhalf d | ∃ φ, IsTestFunction φ ∧ x = toHhalf φ} := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨φ, hφ, h⟩ := exists_test_coord_near (1 / 2) (by norm_num)
    (show HR d from x).2 hr
  refine ⟨toHhalf φ, ?_, φ, hφ, rfl⟩
  rw [Metric.mem_ball]
  change dist (show HR d from toHhalf φ) (show HR d from x) < r
  rw [Subtype.dist_eq, dist_eq_norm, toHhalf_coe hφ]
  exact h

/-- **Density of real tests in `H^{-1/2}`** (UM-0; same proof as `denseRange_toHhalf`). -/
theorem denseRange_toHmhalf :
    Dense {x : Hmhalf d | ∃ φ, IsTestFunction φ ∧ x = toHmhalf φ} := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨φ, hφ, h⟩ := exists_test_coord_near (-1 / 2) (by norm_num)
    (show HR d from x).2 hr
  refine ⟨toHmhalf φ, ?_, φ, hφ, rfl⟩
  rw [Metric.mem_ball]
  change dist (show HR d from toHmhalf φ) (show HR d from x) < r
  rw [Subtype.dist_eq, dist_eq_norm, toHmhalf_coe hφ]
  exact h


/-! ### Multipliers -/

/-- **Uniqueness of the multiplier of `V`** (UM-0): two bounded maps that agree with `φ ↦ Vφ` on
tests coincide (density of tests in `H^{1/2}`). -/
theorem IsMultiplier.unique {V : Rd d → ℝ} {M M' : Hhalf d →L[ℝ] Hmhalf d}
    (h : IsMultiplier V M) (h' : IsMultiplier V M') : M = M' := by
  refine ContinuousLinearMap.coeFn_injective
    (Continuous.ext_on denseRange_toHhalf M.continuous M'.continuous ?_)
  rintro x ⟨φ, hφ, rfl⟩
  rw [h.2 φ hφ, h'.2 φ hφ]

/-- Auxiliary: integrability of `(1 + 4π²|ξ|²)^σ |𝓕φ|²` for a test. -/
theorem integrable_weighted (σ : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    Integrable (fun ξ => (1 + ‖(2 * π) • ξ‖ ^ 2) ^ σ * ‖𝓕 (H1Mathlib.testSchwartz hφ) ξ‖ ^ 2)
      (volume : Measure (Rd d)) := by
  refine (integrable_norm_sq_schwartz (coordSchwartz σ hφ)).congr
    (Eventually.of_forall fun ξ => ?_)
  simp only [coordSchwartz, SchwartzMap.smulLeftCLM_apply_apply (msWeight_growth σ),
    smul_eq_mul, norm_mul, mul_pow, norm_msWeight_sq]

/-- Auxiliary: `‖V φ‖_{H^{-1/2}} ≤ C ‖φ‖_{H^{1/2}}` for a smooth `V` with `|V| ≤ C`. -/
theorem norm_toHmhalf_mul_le {V : Rd d → ℝ} (hV : ContDiff ℝ ∞ V) {C : ℝ}
    (hC : ∀ x, |V x| ≤ C) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ‖toHmhalf (fun x => V x * φ x)‖ ≤ C * ‖toHhalf φ‖ := by
  have hVφ := isTest_smooth_mul hV hφ
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [norm_toHmhalf _ hVφ, norm_toHhalf _ hφ]
  have hpos : ∀ ξ : Rd d, 1 ≤ 1 + ‖(2 * π) • ξ‖ ^ 2 := fun ξ => by
    nlinarith [norm_nonneg ((2 * π) • ξ)]
  have h1 : ‖coord (-1 / 2) (fun x => V x * φ x)‖ ^ 2 ≤
      ∫ x, ‖H1Mathlib.testSchwartz hVφ x‖ ^ 2 := by
    rw [norm_coord_sq _ hVφ, ← SchwartzMap.integral_norm_sq_fourier]
    refine integral_mono (integrable_weighted _ hVφ) (integrable_norm_sq_schwartz _) fun ξ => ?_
    have := Real.rpow_le_one_of_one_le_of_nonpos (hpos ξ) (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
    nlinarith [sq_nonneg ‖𝓕 (H1Mathlib.testSchwartz hVφ) ξ‖]
  have h2 : ∫ x, ‖H1Mathlib.testSchwartz hVφ x‖ ^ 2 ≤
      C ^ 2 * ∫ x, ‖H1Mathlib.testSchwartz hφ x‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_norm_sq_schwartz _)
      ((integrable_norm_sq_schwartz _).const_mul _) fun x => ?_
    simp only [H1Mathlib.testSchwartz_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have := hC x
    have hv : V x ^ 2 ≤ C ^ 2 := by nlinarith [abs_nonneg (V x), sq_abs (V x)]
    nlinarith [sq_nonneg (φ x)]
  have h3 : ∫ x, ‖H1Mathlib.testSchwartz hφ x‖ ^ 2 ≤ ‖coord (1 / 2) φ‖ ^ 2 := by
    rw [norm_coord_sq _ hφ, ← SchwartzMap.integral_norm_sq_fourier]
    refine integral_mono (integrable_norm_sq_schwartz _) (integrable_weighted _ hφ) fun ξ => ?_
    have := Real.one_le_rpow (hpos ξ) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    nlinarith [sq_nonneg ‖𝓕 (H1Mathlib.testSchwartz hφ) ξ‖]
  have h4 : ‖coord (-1 / 2) (fun x => V x * φ x)‖ ^ 2 ≤ (C * ‖coord (1 / 2) φ‖) ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg C]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

/-- **Linearity of `φ ↦ [φ]_{H^{-1/2}}` on tests** (additivity). -/
theorem toHmhalf_add {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    toHmhalf (φ + ψ) = toHmhalf φ + toHmhalf ψ := by
  apply Subtype.ext
  change ((show HR d from toHmhalf (φ + ψ)) : Lp ℂ 2 (volume : Measure (Rd d))) =
    ((show HR d from toHmhalf φ) : Lp ℂ 2 (volume : Measure (Rd d))) +
      ((show HR d from toHmhalf ψ) : Lp ℂ 2 (volume : Measure (Rd d)))
  rw [toHmhalf_coe (isTest_add hφ hψ), toHmhalf_coe hφ, toHmhalf_coe hψ, coord_add _ hφ hψ]

/-- **Linearity of `φ ↦ [φ]_{H^{-1/2}}` on tests** (homogeneity). -/
theorem toHmhalf_smul (c : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    toHmhalf (c • φ) = c • toHmhalf φ := by
  apply Subtype.ext
  change ((show HR d from toHmhalf (c • φ)) : Lp ℂ 2 (volume : Measure (Rd d))) =
    c • ((show HR d from toHmhalf φ) : Lp ℂ 2 (volume : Measure (Rd d)))
  rw [toHmhalf_coe (isTest_smul c hφ), toHmhalf_coe hφ, coord_smul _ _ hφ]; rfl

/-- The real test functions as a subspace. -/
def testSub (d : ℕ) : Submodule ℝ (Rd d → ℝ) where
  carrier := {φ | IsTestFunction φ}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := fun hφ hψ => isTest_add hφ hψ
  smul_mem' := fun c _ hφ => isTest_smul c hφ

/-- `φ ↦ [φ]_{H^{1/2}}` on the test subspace. -/
def toHhalfL : testSub d →ₗ[ℝ] Hhalf d where
  toFun φ := toHhalf (φ : Rd d → ℝ)
  map_add' φ ψ := toHhalf_add φ.2 ψ.2
  map_smul' c φ := toHhalf_smul c φ.2

/-- `φ ↦ [V φ]_{H^{-1/2}}` on the test subspace. -/
def mulL (V : Rd d → ℝ) (hV : ContDiff ℝ ∞ V) : testSub d →ₗ[ℝ] Hmhalf d where
  toFun φ := toHmhalf fun x => V x * (φ : Rd d → ℝ) x
  map_add' φ ψ := by
    have e : (fun x => V x * ((φ + ψ : testSub d) : Rd d → ℝ) x) =
        (fun x => V x * (φ : Rd d → ℝ) x) + fun x => V x * (ψ : Rd d → ℝ) x := by
      funext x; simp [mul_add]
    rw [e, toHmhalf_add (isTest_smooth_mul hV φ.2) (isTest_smooth_mul hV ψ.2)]
  map_smul' c φ := by
    have e : (fun x => V x * ((c • φ : testSub d) : Rd d → ℝ) x) =
        c • fun x => V x * (φ : Rd d → ℝ) x := by
      funext x; simp; ring
    rw [e, toHmhalf_smul c (isTest_smooth_mul hV φ.2)]; rfl

/-- Auxiliary: the test subspace has dense image in `H^{1/2}`. -/
theorem denseRange_toHhalfL : DenseRange (toHhalfL (d := d)) := by
  refine denseRange_toHhalf.mono ?_
  rintro x ⟨φ, hφ, rfl⟩
  exact ⟨⟨φ, hφ⟩, rfl⟩

/-- **Existence of the multiplier of a bounded smooth `V`** (UM-0): `‖Vφ‖_{H^{-1/2}} ≤ ‖Vφ‖₂ ≤ C
‖φ‖₂ ≤ C ‖φ‖_{H^{1/2}}`, then extension from the dense tests; the multiplier has norm at most `C`.
(Meaning of `B_E(m_R h_{Ψ,s})`, `integrated_intrinsic_constant.tex` line 36 at revision edf7085f
(book 1.1.3).) -/
theorem exists_isMultiplier {V : Rd d → ℝ} (hV : ContDiff ℝ ∞ V) {C : ℝ}
    (hC : ∀ x, |V x| ≤ C) : ∃ M, IsMultiplier V M ∧ ‖M‖ ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hb : ∀ φ : testSub d, ‖mulL V hV φ‖ ≤ C * ‖toHhalfL φ‖ := fun φ =>
    norm_toHmhalf_mul_le hV hC φ.2
  refine ⟨(mulL V hV).extendOfNorm toHhalfL, ⟨hV, fun φ hφ => ?_⟩,
    LinearMap.opNorm_extendOfNorm_le denseRange_toHhalfL hC0 hb⟩
  exact LinearMap.extendOfNorm_eq denseRange_toHhalfL ⟨C, hb⟩ ⟨φ, hφ⟩


/-! ### The phase space `E` and `B_E` -/

/-- Auxiliary: `eEquiv (u,v) = (u,v)`. -/
theorem eEquiv_toE (u : Hhalf d) (v : Hmhalf d) : eEquiv (toE u v) = (u, v) := by
  simp [toE]

/-- Auxiliary: every state is `toE` of its components. -/
theorem toE_eEquiv (z : E d) : toE (eEquiv z).1 (eEquiv z).2 = z := by
  simp [toE]

/-- Auxiliary: `toE` is injective. -/
theorem toE_injective {u u' : Hhalf d} {v v' : Hmhalf d} (h : toE u v = toE u' v') :
    u = u' ∧ v = v' := by
  have := congrArg eEquiv h
  rw [eEquiv_toE, eEquiv_toE] at this
  exact Prod.mk.inj this

/-- Auxiliary: `‖(u,v)‖_E² = ‖u‖² + ‖v‖²`. -/
theorem norm_toE_sq (u : Hhalf d) (v : Hmhalf d) : ‖toE u v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (u, v) : WithLp 2 (Hhalf d × Hmhalf d))

/-- Auxiliary: `‖(0,v)‖_E = ‖v‖`. -/
theorem norm_toE_zero_left (v : Hmhalf d) : ‖toE (0 : Hhalf d) v‖ = ‖v‖ := by
  have h := norm_toE_sq (0 : Hhalf d) v
  rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Auxiliary: `‖(u,0)‖_E = ‖u‖`. -/
theorem norm_toE_zero_right (u : Hhalf d) : ‖toE u (0 : Hmhalf d)‖ = ‖u‖ := by
  have h := norm_toE_sq u (0 : Hmhalf d)
  rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Auxiliary: `‖u‖ ≤ ‖(u,v)‖_E`. -/
theorem norm_le_norm_toE (u : Hhalf d) (v : Hmhalf d) : ‖u‖ ≤ ‖toE u v‖ := by
  have h := norm_toE_sq u v
  have h2 : ‖u‖ ^ 2 ≤ ‖toE u v‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖v‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- **`B_E(M)(u,v) = (0, M u)`** (`integrated_intrinsic_constant.tex` lines 10-11 at revision
edf7085f (book 1.1.3)). -/
theorem BE_apply (M : Hhalf d →L[ℝ] Hmhalf d) (u : Hhalf d) (v : Hmhalf d) :
    BE M (toE u v) = toE 0 (M u) := by
  simp [BE, toE]

/-- Auxiliary: `B_E(M) z = (0, M z₁)`. -/
theorem BE_apply' (M : Hhalf d →L[ℝ] Hmhalf d) (z : E d) :
    BE M z = toE 0 (M (eEquiv z).1) := by
  rw [← BE_apply M (eEquiv z).1 (eEquiv z).2, toE_eEquiv]

/-- **`B_E` is linear** (difference form). -/
theorem BE_sub (M M' : Hhalf d →L[ℝ] Hmhalf d) : BE (M - M') = BE M - BE M' := by
  ext1 z
  rw [sub_apply, BE_apply', BE_apply', BE_apply',
    sub_apply]
  apply (eEquiv (d := d)).injective
  rw [map_sub, eEquiv_toE, eEquiv_toE, eEquiv_toE]
  simp

/-- **`‖B_E(M)‖ = ‖M‖`** (the norm equality of `L:uniform-E-lift`, `integrated_uniform_products.tex`
lines 34-35 and 50-51 at revision edf7085f (book 1.1.3)). -/
theorem norm_BE (M : Hhalf d →L[ℝ] Hmhalf d) : ‖BE M‖ = ‖M‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    rw [BE_apply', norm_toE_zero_left]
    calc ‖M (eEquiv z).1‖ ≤ ‖M‖ * ‖(eEquiv z).1‖ := M.le_opNorm _
      _ ≤ ‖M‖ * ‖z‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have := norm_le_norm_toE (eEquiv z).1 (eEquiv z).2
          rwa [toE_eEquiv] at this
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    have h := (BE M).le_opNorm (toE u 0)
    rwa [BE_apply, norm_toE_zero_left, norm_toE_zero_right] at h

/-- **`B_E` is injective.** -/
theorem BE_injective : Function.Injective (BE (d := d)) := by
  intro M M' h
  ext1 u
  have := congrArg (fun L : E d →L[ℝ] E d => L (toE u 0)) h
  simp only [BE_apply] at this
  exact (toE_injective this).2

/-- Auxiliary: `B_E` is an isometry (`‖B_E M - B_E M'‖ = ‖M - M'‖`). -/
theorem isometry_BE : Isometry (BE (d := d)) := by
  refine Isometry.of_dist_eq fun M M' => ?_
  rw [dist_eq_norm, dist_eq_norm, ← BE_sub, norm_BE]

end StratonovichHAMSecondMoment.UniformMeanInterface
