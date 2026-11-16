module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The package's weak-gradient `H^1(ℝ^d; ℝ)` identified with Mathlib's Bessel-potential space
`H^{1,2}` (wave L13, item K5a; the D8-lite foundation). Foundation item: no manuscript label of
its own.

Manuscript anchors (revision 39f2597a):
* `notes/notes_stratonovich_ham_second_moment.tex`, lines 748-750: `H^1(ℝ^d; ℝ)` is "the real
  Sobolev space of square-integrable functions with square-integrable first weak derivatives".
  This is `WeakSobolev.MemH1`, reused here unchanged.
* `notes/integrated_signed_static.tex`, Proposition `P:signed-closed-form` (lines 49-67) and its
  proof, line 85: `q_V = z² - b² - v_V(u,u)` with `z = ‖u‖_{H^1}`, `b = ‖u‖₂`, so the
  manuscript's norm is `‖u‖²_{H^1} = ‖u‖₂² + ‖∇u‖₂²` (no `2π`). It is `manuscriptH1NormSq`.
* `notes/integrated_spatial_occupation.tex`, proof of `P:spatial-four-linear`, lines 352-356
  ("Smooth compact functions are dense in `H^1`"), and
  `notes/integrated_unmasked_variational.tex`, line 177 ("Fourier cutoffs give its density in
  `H^1`").

Mathlib's convention. `𝓕` uses `e^{-2πi⟪x, ξ⟫}`, so `∂_j` is the multiplier `2πi ξ_j` and the
Bessel potential `J^s = 𝓕⁻¹ (1 + ‖ξ‖²)^{s/2} 𝓕` is `(1 - (2π)⁻² Δ)^{s/2}`. Hence Mathlib's
`H^{1}` norm is `‖f‖₂² + (2π)⁻² ‖∇f‖₂²`. Decision 5 of wave L13: manuscript constants use
`manuscriptH1NormSq`, never the `BesselPotentialSpace` norm. The two are equivalent with
constants `1` and `(2π)²` (`norm_toH1_sq_le_manuscript`).

Formalized here, unconditionally (no supplied inputs, no added hypotheses):
* `toL2C`, `toDistr`: a real `f ∈ L²` as an element of `L²(ℝ^d; ℂ)` and as the tempered
  distribution `T_f(χ) = ∫ χ f`; `testSchwartz`: a real test function as a Schwartz function.
* `lineDeriv_toDistr`: an `L²` weak gradient `g` of `f` is its distributional gradient,
  `∂_v T_f = T_{⟪g, v⟫}`.
* `memH1_iff_memSobolev` (both directions proved, so the plan's fallback input `H1Converse` is
  not needed): for real `f ∈ L²`, `MemH1 f ↔ MemSobolev 1 2 (toDistr hf)`. Forward:
  `memSobolev_of_hasWeakGradient`; converse: `exists_weakGradient_of_memSobolev`.
* `norm_sq_of_besselPotential_eq`, `norm_toH1_sq`: `‖f‖²_{H^{1}} = ‖f‖₂² + (2π)⁻² ‖g‖₂²` for
  the bundled element `toH1 h : H^{1}(ℝ^d)`.
* `exists_test_tendsto_toH1`: real test functions are dense, in Mathlib's `H^{1}` norm, among
  the real `H^1` profiles. `exists_schwartz_tendsto`: Schwartz functions are dense in
  `H^{s}(ℝ^d)` for every real `s` and complex-valued elements.
* `integral_norm_grad_sq_pos`: a nonzero test function on `ℝ^d`, `d ≥ 1`, has positive gradient
  energy (used by the refutations).
* `h1_identification_paper`: the wrapper with the manuscript's only hypothesis (`f` real and
  square-integrable); the hypothesis is used (it is needed to form `toDistr hf`).

Lean proof route (the lemmas called "Auxiliary to the Lean proof route" serve only this route):
1. Weak gradient to distributional gradient: the weak-gradient identity is extended from test
   functions to smooth `h` with `h, ∇h ∈ L²` by `H1Density`'s cutoffs (`weak_smooth`), then to
   complex Schwartz functions through their real and imaginary parts (`weak_schwartz`).
2. Forward direction: the symbol identity `⟨ξ⟩ = ⟨ξ⟩⁻¹ + Σ_j ξ_j (ξ_j ⟨ξ⟩⁻¹)`
   (`besSym_one_eq`) writes `J¹ T_f` as `J⁻¹ T_f` plus bounded Fourier multipliers of the
   `L²` distributions `ξ_j T_f = (2πi)⁻¹ ∂_j T_f` (`besselPotential_one_eq`).
3. Converse: Mathlib's `MemSobolev.lineDerivOp` gives `∂_j T_f = T_{G_j}` with `G_j ∈ L²(ℂ)`;
   the real field `Σ_j Re G_j e_j` is a weak gradient (`weak_coord_of_eq`).
4. Norm: on the Fourier side `𝓕 W = ⟨ξ⟩ 𝓕 f` and `𝓕 (∂_j f) = 2πi ξ_j 𝓕 f` almost everywhere
   (`ae_eq_of_smulLeft`), then Plancherel (`Lp.norm_fourier_eq`).
5. Density: the norm identity applied to `φ_n - f` with `H1Density.h1TestDense`; Schwartz
   density by applying `J^{-s}` to Schwartz approximants of `J^s u` in `L²`.

Not formalized: the density of complex-valued `C_c^∞` in the complex `H^{1}(ℝ^d)` (only real
profiles; for complex elements only the Schwartz density is proved); the separability remark of
`P:spatial-four-linear` (lines 356-358); a gradient map on the bundled complex space. The
restatement of `P:spatial-four-linear` and later results on Mathlib's `H^1` is not part of this
item.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.WeakSobolev
public import StratonovichHAMSecondMoment.VariationalFloor
public import StratonovichHAMSecondMoment.H1Density

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real

namespace StratonovichHAMSecondMoment.H1Mathlib

open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)

variable {d : ℕ}

/-! ### Real `L²` functions as tempered distributions -/

/-- The complexification `x ↦ (f x : ℂ)` of a real `f ∈ L²` as an element of `L²(ℝ^d; ℂ)`. -/
def toL2C {f : Rd d → ℝ} (hf : MemLp f 2 volume) : Lp ℂ 2 (volume : Measure (Rd d)) :=
  hf.ofReal.toLp _

/-- Auxiliary to the Lean proof route: `toL2C hf` is `x ↦ (f x : ℂ)` almost everywhere. -/
theorem coeFn_toL2C {f : Rd d → ℝ} (hf : MemLp f 2 volume) :
    (toL2C hf : Rd d → ℂ) =ᵐ[volume] fun x => (f x : ℂ) :=
  hf.ofReal.coeFn_toLp

/-- The tempered distribution `T_f(χ) = ∫ χ f` of a real `f ∈ L²` (complexified). -/
def toDistr {f : Rd d → ℝ} (hf : MemLp f 2 volume) : 𝓢'(Rd d, ℂ) :=
  (toL2C hf : 𝓢'(Rd d, ℂ))

/-- The pairing of `T_f` with a Schwartz function: `T_f(χ) = ∫ χ(x) f(x) dx`. -/
theorem toDistr_apply {f : Rd d → ℝ} (hf : MemLp f 2 volume) (χ : 𝓢(Rd d, ℂ)) :
    toDistr hf χ = ∫ x, χ x * (f x : ℂ) := by
  simp only [toDistr, Lp.toTemperedDistribution_apply, smul_eq_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2C hf] with x hx
  rw [hx]

/-- A real test function `φ ∈ C_c^∞(ℝ^d; ℝ)`, complexified, as a Schwartz function. -/
def testSchwartz {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : 𝓢(Rd d, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => (φ x : ℂ))
    (hφ.2.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hφ.1)

/-- Auxiliary to the Lean proof route: `testSchwartz hφ` is `x ↦ (φ x : ℂ)`. -/
@[simp]
theorem testSchwartz_apply {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (x : Rd d) :
    testSchwartz hφ x = (φ x : ℂ) := rfl

/-- Auxiliary to the Lean proof route: the derivative of the complexification
is the complexified derivative. -/
theorem fderiv_ofReal_apply {φ : Rd d → ℝ} {x : Rd d} (hφ : DifferentiableAt ℝ φ x)
    (v : Rd d) : fderiv ℝ (fun y => (φ y : ℂ)) x v = (fderiv ℝ φ x v : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := φ x)).comp x hφ.hasFDerivAt
  rw [show (fun y => (φ y : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, h.fderiv]
  simp

/-- Auxiliary to the Lean proof route: `∂_v` of the complexified test function is
the complexified classical derivative `Dφ(x) v`. -/
theorem lineDeriv_testSchwartz_apply {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (v x : Rd d) :
    (∂_{v} (testSchwartz hφ)) x = (fderiv ℝ φ x v : ℂ) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact fderiv_ofReal_apply ((hφ.1.differentiable (by simp)) x) v

/-! ### The weak-gradient identity against smooth and Schwartz functions -/

/-- Auxiliary to the Lean proof route: `x ↦ ⟪g x, v⟫` is in `L²` when `g` is. -/
theorem memLp_inner {g : Rd d → Rd d} (hg : MemLp g 2 volume) (v : Rd d) :
    MemLp (fun x => inner ℝ (g x) v) 2 volume := by
  refine ((innerSL ℝ v).comp_memLp' hg).congr_norm hg.aestronglyMeasurable.inner_const
    (Eventually.of_forall fun x => ?_)
  simp [real_inner_comm]

/-- `x ↦ Du(x) v` is in `L²` when `∇u` is. -/
theorem memLp_fderiv_apply {u : Rd d → ℝ} (hu : MemLp (grad u) 2 volume) (v : Rd d) :
    MemLp (fun x => fderiv ℝ u x v) 2 volume :=
  (memLp_inner hu v).congr_norm
    ((memLp_inner hu v).aestronglyMeasurable.congr (Eventually.of_forall fun x => by
      simp [grad, InnerProductSpace.toDual_symm_apply]))
    (Eventually.of_forall fun x => by simp [grad, InnerProductSpace.toDual_symm_apply])

/-- The weak-gradient identity extends from test functions to smooth `h` with
`h, ∇h ∈ L²` (cutoff approximation, `H1Density.tendsto_cutoff_test`). -/
theorem weak_smooth {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) {h : Rd d → ℝ}
    (hh : ContDiff ℝ ∞ h) (hL : MemLp h 2 volume) (hG : MemLp (grad h) 2 volume) (v : Rd d) :
    ∫ x, f x * fderiv ℝ h x v = -∫ x, inner ℝ (g x) v * h x := by
  obtain ⟨C1, C2⟩ := H1Density.tendsto_cutoff_test hh hL hG
  set ψ : ℕ → Rd d → ℝ := fun n x => H1Density.cutoff n x * h x
  have hψ : ∀ n, IsTestFunction (ψ n) := fun n => H1Density.cutoff_isTest n hh
  have hfd : ∀ (u : Rd d → ℝ) x, fderiv ℝ u x v = inner ℝ (grad u x) v := by
    intro u x
    simp [grad, InnerProductSpace.toDual_symm_apply]
  have hM : Tendsto (fun n => ENNReal.ofReal ‖v‖ *
      eLpNorm (fun x => grad (ψ n) x - grad h x) 2 volume) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul C2 (Or.inr (ENNReal.ofReal_ne_top (r := ‖v‖)))
    rwa [mul_zero] at this
  have hB : Tendsto (fun n => eLpNorm (fun x => inner ℝ (grad (ψ n) x) v -
      inner ℝ (grad h x) v) 2 volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hM
      (fun _ => zero_le) (fun n => ?_)
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x => ?_) 2
    · exact ((memLp_inner (VariationalFloor.memLp_grad (hψ n)) v).sub
        (memLp_inner hG v)).aestronglyMeasurable
    · rw [← inner_sub_left, mul_comm]
      exact (Real.norm_eq_abs _).trans_le (abs_real_inner_le_norm _ _)
  have A := H1Density.tendsto_integral_mul_of_L2
    (fun n => memLp_inner (VariationalFloor.memLp_grad (hψ n)) v) (memLp_inner hG v) hf hB
  have B := H1Density.tendsto_integral_mul_of_L2
    (fun n => VariationalFloor.memLp_test (hψ n)) hL (memLp_inner hg v) C1
  have L1 : Tendsto (fun n => ∫ x, f x * fderiv ℝ (ψ n) x v) atTop
      (𝓝 (∫ x, f x * fderiv ℝ h x v)) := by
    have e1 : ∀ n, ∫ x, f x * fderiv ℝ (ψ n) x v = ∫ x, inner ℝ (grad (ψ n) x) v * f x :=
      fun n => by congr 1; funext x; rw [hfd]; ring
    have e2 : ∫ x, f x * fderiv ℝ h x v = ∫ x, inner ℝ (grad h x) v * f x := by
      congr 1; funext x; rw [hfd]; ring
    rw [e2]; exact A.congr fun n => (e1 n).symm
  have L2 : Tendsto (fun n => ∫ x, f x * fderiv ℝ (ψ n) x v) atTop
      (𝓝 (-∫ x, inner ℝ (g x) v * h x)) := by
    have e : ∀ n, ∫ x, f x * fderiv ℝ (ψ n) x v = -∫ x, ψ n x * inner ℝ (g x) v := fun n => by
      rw [hw _ (hψ n) v]; congr 2; funext x; ring
    have e' : ∫ x, inner ℝ (g x) v * h x = ∫ x, h x * inner ℝ (g x) v := by
      congr 1; funext x; ring
    rw [e']; exact B.neg.congr fun n => (e n).symm
  exact tendsto_nhds_unique L1 L2

/-- Auxiliary: integral of `(a + b i) F` for real `a, b, F` with `a F, b F` integrable. -/
theorem integral_reIm_mul {a b F : Rd d → ℝ} (ha : Integrable (fun x => a x * F x) volume)
    (hb : Integrable (fun x => b x * F x) volume) :
    ∫ x, ((a x : ℂ) + (b x : ℂ) * Complex.I) * (F x : ℂ) =
      ((∫ x, a x * F x : ℝ) : ℂ) + ((∫ x, b x * F x : ℝ) : ℂ) * Complex.I := by
  have e : (fun x => ((a x : ℂ) + (b x : ℂ) * Complex.I) * (F x : ℂ)) =
      fun x => ((a x * F x : ℝ) : ℂ) + ((b x * F x : ℝ) : ℂ) * Complex.I := by
    funext x; push_cast; ring
  rw [e, integral_add ha.ofReal (hb.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal,
    integral_complex_ofReal]

/-- Real and imaginary parts of a Schwartz function: smooth, in `L²`, gradient in `L²`. -/
theorem schwartz_part {χ : 𝓢(Rd d, ℂ)} (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ContDiff ℝ ∞ (fun x => L (χ x)) ∧ MemLp (fun x => L (χ x)) 2 volume ∧
      MemLp (grad fun x => L (χ x)) 2 volume ∧
      ∀ x v, fderiv ℝ (fun y => L (χ y)) x v = L (fderiv ℝ χ x v) := by
  have hs : ContDiff ℝ ∞ χ := χ.smooth ⊤
  have hc : ContDiff ℝ ∞ (fun x => L (χ x)) := L.contDiff.comp hs
  have hfd : ∀ x, fderiv ℝ (fun y => L (χ y)) x = L.comp (fderiv ℝ χ x) := fun x =>
    (L.hasFDerivAt.comp x ((hs.differentiable (by simp)) x).hasFDerivAt).fderiv
  refine ⟨hc, L.comp_memLp' (χ.memLp 2), ?_, fun x v => by rw [hfd]; rfl⟩
  have hD : MemLp (fun x => ‖fderiv ℝ χ x‖) 2 volume := by
    have := ((SchwartzMap.fderivCLM ℝ (Rd d) ℂ χ).memLp 2 (μ := volume)).norm
    simpa only [SchwartzMap.fderivCLM_apply] using this
  refine hD.of_le ?_ (Eventually.of_forall fun x => ?_)
  · exact ((InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp
      (hc.continuous_fderiv (by simp))).aestronglyMeasurable
  · simp only [grad, LinearIsometryEquiv.norm_map, hfd, norm_norm]
    calc ‖L.comp (fderiv ℝ χ x)‖ ≤ ‖L‖ * ‖fderiv ℝ χ x‖ := L.opNorm_comp_le _
      _ ≤ 1 * ‖fderiv ℝ χ x‖ := by gcongr
      _ = ‖fderiv ℝ χ x‖ := one_mul _

/-- The weak-gradient identity against a complex Schwartz function:
`∫ (∂_v χ) f = -∫ χ ⟪g, v⟫`. -/
theorem weak_schwartz {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) (χ : 𝓢(Rd d, ℂ)) (v : Rd d) :
    ∫ x, fderiv ℝ χ x v * (f x : ℂ) = -∫ x, χ x * (inner ℝ (g x) v : ℂ) := by
  obtain ⟨rs, rL, rG, rd⟩ := schwartz_part (χ := χ) Complex.reCLM (by simp)
  obtain ⟨is, iL, iG, id⟩ := schwartz_part (χ := χ) Complex.imCLM (by simp)
  have hG := memLp_inner hg v
  have e1 : (fun x => fderiv ℝ χ x v * (f x : ℂ)) = fun x =>
      ((fderiv ℝ (fun y => Complex.reCLM (χ y)) x v : ℂ) +
        (fderiv ℝ (fun y => Complex.imCLM (χ y)) x v : ℂ) * Complex.I) * (f x : ℂ) := by
    funext x; rw [rd, id]; simp [Complex.re_add_im]
  have e2 : (fun x => χ x * (inner ℝ (g x) v : ℂ)) = fun x =>
      ((Complex.reCLM (χ x) : ℂ) + (Complex.imCLM (χ x) : ℂ) * Complex.I) *
        (inner ℝ (g x) v : ℂ) := by
    funext x; simp [Complex.re_add_im]
  have hdr := fun u (hu : MemLp (grad u) 2 volume) => memLp_fderiv_apply hu v
  rw [e1, e2, integral_reIm_mul ((hdr _ rG).integrable_mul hf) ((hdr _ iG).integrable_mul hf),
    integral_reIm_mul (rL.integrable_mul hG) (iL.integrable_mul hG)]
  have wr := weak_smooth hf hg hw rs rL rG v
  have wi := weak_smooth hf hg hw is iL iG v
  have c1 : ∫ x, fderiv ℝ (fun y => Complex.reCLM (χ y)) x v * f x =
      -∫ x, Complex.reCLM (χ x) * inner ℝ (g x) v := by
    rw [show (fun x => fderiv ℝ (fun y => Complex.reCLM (χ y)) x v * f x) =
      fun x => f x * fderiv ℝ (fun y => Complex.reCLM (χ y)) x v from by funext x; ring, wr]
    congr 2; funext x; ring
  have c2 : ∫ x, fderiv ℝ (fun y => Complex.imCLM (χ y)) x v * f x =
      -∫ x, Complex.imCLM (χ x) * inner ℝ (g x) v := by
    rw [show (fun x => fderiv ℝ (fun y => Complex.imCLM (χ y)) x v * f x) =
      fun x => f x * fderiv ℝ (fun y => Complex.imCLM (χ y)) x v from by funext x; ring, wi]
    congr 2; funext x; ring
  rw [c1, c2]; push_cast; ring

/-! ### Weak gradient = distributional gradient -/

/-- **Bridge.** If `g ∈ L²` is a weak gradient of the real `f ∈ L²`, then the
distributional directional derivative of `T_f` in direction `v` is `T_{⟪g, v⟫}`. -/
theorem lineDeriv_toDistr {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) (v : Rd d) :
    ∂_{v} (toDistr hf) = toDistr (memLp_inner hg v) := by
  ext χ
  rw [lineDerivOp_apply_apply, toDistr_apply, toDistr_apply]
  have e : (fun x => (-∂_{v} χ) x * (f x : ℂ)) = fun x => -(fderiv ℝ χ x v * (f x : ℂ)) := by
    funext x
    rw [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, neg_mul]
  rw [e, integral_neg, weak_schwartz hf hg hw χ v, neg_neg]

/-! ### Fourier symbols -/

/-- The standard orthonormal basis `e_j` of `ℝ^d`. -/
abbrev eb (d : ℕ) : OrthonormalBasis (Fin d) ℝ (Rd d) := EuclideanSpace.basisFun (Fin d) ℝ

/-- The Bessel symbol `⟨ξ⟩^s = (1 + ‖ξ‖²)^{s/2}` (complexified), as in Mathlib's
`besselPotential`. -/
def besSym (d : ℕ) (s : ℝ) (ξ : Rd d) : ℂ := (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)

/-- The coordinate symbol `ξ ↦ ⟪ξ, e_j⟫`. -/
def coordSym (j : Fin d) (ξ : Rd d) : ℂ := ((inner ℝ ξ (eb d j) : ℝ) : ℂ)

/-- The bounded symbol `ξ ↦ ⟪ξ, e_j⟫ ⟨ξ⟩^{-1}`. -/
def rieszSym (j : Fin d) (ξ : Rd d) : ℂ :=
  ((inner ℝ ξ (eb d j) * (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)

/-- Auxiliary to the Lean proof route: the Bessel symbol has temperate growth. -/
theorem besSym_growth (s : ℝ) : (besSym d s).HasTemperateGrowth := by
  unfold besSym; fun_prop

/-- Auxiliary to the Lean proof route: the coordinate symbol has temperate growth. -/
theorem coordSym_growth (j : Fin d) : (coordSym j).HasTemperateGrowth := by
  unfold coordSym; fun_prop

/-- Auxiliary to the Lean proof route: the bounded symbol has temperate growth. -/
theorem rieszSym_growth (j : Fin d) : (rieszSym j).HasTemperateGrowth := by
  unfold rieszSym; fun_prop

/-- Auxiliary to the Lean proof route: `Σ_j ⟪ξ, e_j⟫² = ‖ξ‖²`. -/
theorem sum_sq_coord (ξ : Rd d) : ∑ j, inner ℝ ξ (eb d j) ^ 2 = ‖ξ‖ ^ 2 := by
  rw [← (eb d).sum_sq_inner_left ξ]

/-- Auxiliary to the Lean proof route: `a^{-1/2} a = a^{1/2}` for `a > 0`. -/
theorem rpow_neg_half_mul {a : ℝ} (ha : 0 < a) : a ^ ((-1 : ℝ) / 2) * a = a ^ ((1 : ℝ) / 2) := by
  conv_lhs => rhs; rw [← Real.rpow_one a]
  rw [← Real.rpow_add ha]; norm_num

/-- The symbol identity `⟨ξ⟩ = ⟨ξ⟩^{-1} + Σ_j ξ_j (ξ_j ⟨ξ⟩^{-1})`. -/
theorem besSym_one_eq (ξ : Rd d) :
    besSym d 1 ξ = besSym d (-1) ξ + ∑ j, coordSym j ξ * rieszSym j ξ := by
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  simp only [besSym, coordSym, rieszSym]
  rw [show ((-1 : ℝ) / 2) = (-1 : ℝ) / 2 from rfl]
  have : ((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) = (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) +
      ∑ j, inner ℝ ξ (eb d j) * (inner ℝ ξ (eb d j) * (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2)) := by
    have e : ∀ j, inner ℝ ξ (eb d j) * (inner ℝ ξ (eb d j) * (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2)) =
        inner ℝ ξ (eb d j) ^ 2 * (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) := fun j => by ring
    simp_rw [e]
    rw [← Finset.sum_mul, sum_sq_coord, ← one_add_mul, mul_comm, rpow_neg_half_mul hpos]
  rw [show ((1 : ℝ) / 2) = 1 / 2 from rfl] at this
  have h2 : ((-1 : ℝ) / 2) = -1 / 2 := by norm_num
  rw [h2] at this ⊢
  exact_mod_cast this

/-- Auxiliary to the Lean proof route: the symbol `ξ_j ⟨ξ⟩^{-1}` is bounded by `1`. -/
theorem norm_rieszSym_le (j : Fin d) (ξ : Rd d) : ‖rieszSym j ξ‖ ≤ 1 := by
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hs : (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) = (Real.sqrt (1 + ‖ξ‖ ^ 2))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hpos.le]; norm_num
  have hle : ‖ξ‖ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hsq : 0 < Real.sqrt (1 + ‖ξ‖ ^ 2) := Real.sqrt_pos.mpr hpos
  simp only [rieszSym, Complex.norm_real, Real.norm_eq_abs, hs, abs_mul, abs_inv,
    abs_of_pos hsq]
  rw [← div_eq_mul_inv, div_le_one hsq]
  calc |inner ℝ ξ (eb d j)| ≤ ‖ξ‖ * ‖eb d j‖ := abs_real_inner_le_norm _ _
    _ = ‖ξ‖ := by simp
    _ ≤ _ := hle

/-- `𝓕⁻(ξ_j 𝓕 T) = (2πi)⁻¹ ∂_{e_j} T` (Mathlib's Fourier convention). -/
theorem coordSym_eq_lineDeriv (j : Fin d) (T : 𝓢'(Rd d, ℂ)) :
    fourierMultiplierCLM ℂ (coordSym j) T = (2 * π * Complex.I)⁻¹ • ∂_{eb d j} T := by
  have hne : (2 * π * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [lineDeriv_eq_fourierMultiplierCLM, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rfl

/-- Additivity of Fourier multipliers in the symbol (on `𝓢'`). -/
theorem fourierMultiplier_add {g₁ g₂ : Rd d → ℂ} (h₁ : g₁.HasTemperateGrowth)
    (h₂ : g₂.HasTemperateGrowth) (T : 𝓢'(Rd d, ℂ)) :
    fourierMultiplierCLM ℂ (g₁ + g₂) T =
      fourierMultiplierCLM ℂ g₁ T + fourierMultiplierCLM ℂ g₂ T := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add h₁ h₂, add_apply,
    FourierTransform.fourierInv_add]

/-- The Bessel potential of order one, decomposed: `J¹T = J⁻¹T + Σ_j R_j (ξ_j T)`. -/
theorem besselPotential_one_eq (T : 𝓢'(Rd d, ℂ)) :
    besselPotential (Rd d) ℂ 1 T = besselPotential (Rd d) ℂ (-1) T +
      ∑ j, fourierMultiplierCLM ℂ (rieszSym j) (fourierMultiplierCLM ℂ (coordSym j) T) := by
  have hsym : (fun x : Rd d => (((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) =
      besSym d (-1) + fun x => ∑ j, (coordSym j * rieszSym j) x := by
    funext x; exact besSym_one_eq x
  have hg : ∀ j ∈ Finset.univ, (coordSym (d := d) j * rieszSym j).HasTemperateGrowth :=
    fun j _ => (coordSym_growth j).mul (rieszSym_growth j)
  simp only [besselPotential]
  rw [hsym, fourierMultiplier_add (besSym_growth _) (by
      have := Function.HasTemperateGrowth.sum (s := Finset.univ) hg
      simpa using this),
    fourierMultiplierCLM_sum ℂ hg, sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (coordSym_growth j) (rieszSym_growth j)]

/-- An `L²` element defines an order-zero Sobolev distribution. -/
theorem memSobolev_zero_toDistr {f : Rd d → ℝ} (hf : MemLp f 2 volume) :
    MemSobolev 0 2 (toDistr hf) :=
  memSobolev_zero_iff.mpr ⟨toL2C hf, rfl⟩

/-- **Forward direction.** A real `f ∈ L²` with an `L²` weak gradient lies in
Mathlib's `H^1 = H^{1,2}`. -/
theorem memSobolev_of_hasWeakGradient {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) :
    MemSobolev 1 2 (toDistr hf) := by
  have h0 : MemSobolev 0 2 (besselPotential (Rd d) ℂ 1 (toDistr hf)) := by
    rw [besselPotential_one_eq]
    refine MemSobolev.add ?_ ?_
    · rw [memSobolev_besselPotential_iff]
      exact (memSobolev_zero_toDistr hf).mono (by norm_num)
    · refine Finset.sum_induction _ (MemSobolev 0 2) (fun _ _ => MemSobolev.add)
        (memSobolev_fun_zero _ _ _ _) fun j _ => ?_
      refine MemSobolev.fourierMultiplierCLM_of_bounded ?_ (rieszSym_growth j)
        ⟨1, norm_rieszSym_le j⟩
      rw [coordSym_eq_lineDeriv, lineDeriv_toDistr hf hg hw]
      exact (memSobolev_zero_toDistr _).smul _
  rw [memSobolev_besselPotential_iff, add_zero] at h0
  exact h0

/-- The real vector field `x ↦ Σ_j Re G_j(x) e_j` built from complex `L²` components. -/
def reField (G : Fin d → Lp ℂ 2 (volume : Measure (Rd d))) (x : Rd d) : Rd d :=
  ∑ j, (G j x).re • eb d j

/-- Auxiliary to the Lean proof route: `reField G ∈ L²`. -/
theorem memLp_reField (G : Fin d → Lp ℂ 2 (volume : Measure (Rd d))) :
    MemLp (reField G) 2 volume := by
  refine memLp_finsetSum Finset.univ fun j _ => ?_
  have h : MemLp (fun x => (G j x).re) 2 volume := by
    simpa using (Lp.memLp (G j)).re
  exact (ContinuousLinearMap.toSpanSingleton ℝ (eb d j)).comp_memLp' h

/-- Auxiliary to the Lean proof route: `⟪reField G x, v⟫ = Σ_j Re G_j(x) ⟪e_j, v⟫`. -/
theorem inner_reField (G : Fin d → Lp ℂ 2 (volume : Measure (Rd d))) (x v : Rd d) :
    inner ℝ (reField G x) v = ∑ j, (G j x).re * inner ℝ (eb d j) v := by
  simp [reField, sum_inner, real_inner_smul_left]

/-- Pairing a real test function with `∂_{e_j} T_f` and with an `L²` function `G`. -/
theorem weak_coord_of_eq {f : Rd d → ℝ} (hf : MemLp f 2 volume) (j : Fin d)
    (G : Lp ℂ 2 (volume : Measure (Rd d)))
    (hG : ∂_{eb d j} (toDistr hf) = (G : 𝓢'(Rd d, ℂ))) {φ : Rd d → ℝ}
    (hφ : IsTestFunction φ) :
    ∫ x, f x * fderiv ℝ φ x (eb d j) = -∫ x, (G x).re * φ x := by
  have h := congrArg (fun T : 𝓢'(Rd d, ℂ) => T (testSchwartz hφ)) hG
  simp only [lineDerivOp_apply_apply, toDistr_apply, Lp.toTemperedDistribution_apply] at h
  have e1 : (fun x => (-∂_{eb d j} (testSchwartz hφ)) x * (f x : ℂ)) =
      fun x => -(((fderiv ℝ φ x (eb d j) * f x : ℝ)) : ℂ) := by
    funext x; rw [neg_apply, lineDeriv_testSchwartz_apply]; push_cast; ring
  rw [e1, integral_neg, integral_complex_ofReal] at h
  have hint : Integrable (fun x => testSchwartz hφ x • G x) volume := by
    exact (VariationalFloor.memLp_test hφ).ofReal.integrable_mul (Lp.memLp G)
  have h2 := congrArg Complex.re h
  rw [← RCLike.re_eq_complex_re, ← integral_re hint] at h2
  simp only [Complex.neg_re, Complex.ofReal_re, testSchwartz_apply, smul_eq_mul,
    RCLike.re_to_complex, Complex.re_ofReal_mul] at h2
  have e2 : ∫ x, f x * fderiv ℝ φ x (eb d j) = ∫ x, fderiv ℝ φ x (eb d j) * f x := by
    congr 1; funext x; ring
  have e3 : ∫ x, (G x).re * φ x = ∫ x, φ x * (G x).re := by
    congr 1; funext x; ring
  rw [e2, e3, ← h2, neg_neg]

/-- **Converse direction.** A real `f ∈ L²` whose distribution lies in Mathlib's
`H^1` has an `L²` weak gradient. -/
theorem exists_weakGradient_of_memSobolev {f : Rd d → ℝ} (hf : MemLp f 2 volume)
    (h : MemSobolev 1 2 (toDistr hf)) :
    ∃ g : Rd d → Rd d, MemLp g 2 volume ∧ HasWeakGradient f g := by
  have hj : ∀ j : Fin d, ∃ G : Lp ℂ 2 (volume : Measure (Rd d)),
      ∂_{eb d j} (toDistr hf) = (G : 𝓢'(Rd d, ℂ)) := fun j => by
    have := h.lineDerivOp (m := eb d j)
    rw [sub_self] at this
    exact memSobolev_zero_iff.mp this
  choose G hG using hj
  refine ⟨reField G, memLp_reField G, fun φ hφ v => ?_⟩
  have hc := fun j => weak_coord_of_eq hf j (G j) (hG j) hφ
  have hv : ∀ x, fderiv ℝ φ x v = ∑ j, inner ℝ (eb d j) v * fderiv ℝ φ x (eb d j) := by
    intro x
    conv_lhs => rw [← (eb d).sum_repr' v]
    simp [map_sum, map_smul, smul_eq_mul]
  have i1 : ∀ j ∈ Finset.univ, Integrable
      (fun x => f x * (inner ℝ (eb d j) v * fderiv ℝ φ x (eb d j))) volume := fun j _ => by
    have := hf.integrable_mul
      ((memLp_fderiv_apply (VariationalFloor.memLp_grad hφ) (eb d j)).const_mul
        (inner ℝ (eb d j) v))
    exact this
  have i2 : ∀ j ∈ Finset.univ, Integrable
      (fun x => (G j x).re * inner ℝ (eb d j) v * φ x) volume := fun j _ => by
    have hre : MemLp (fun x => (G j x).re) 2 volume := by simpa using (Lp.memLp (G j)).re
    exact (hre.mul_const _).integrable_mul (VariationalFloor.memLp_test hφ)
  have l1 : ∫ x, f x * fderiv ℝ φ x v =
      ∑ j, inner ℝ (eb d j) v * ∫ x, f x * fderiv ℝ φ x (eb d j) := by
    simp_rw [hv, Finset.mul_sum]
    rw [integral_finsetSum _ i1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]; congr 1; funext x; ring
  have l2 : ∫ x, inner ℝ (reField G x) v * φ x =
      ∑ j, inner ℝ (eb d j) v * ∫ x, (G j x).re * φ x := by
    simp_rw [inner_reField, Finset.sum_mul]
    rw [integral_finsetSum _ i2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [l1, l2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc j]; ring

/-- **The `H^1` identification (K5a).** For real `f ∈ L²`: `f ∈ H^1` in the weak-gradient
sense (`WeakSobolev.MemH1`) iff its distribution lies in Mathlib's `H^{1,2}`. -/
theorem memH1_iff_memSobolev {f : Rd d → ℝ} (hf : MemLp f 2 volume) :
    MemH1 f ↔ MemSobolev 1 2 (toDistr hf) := by
  constructor
  · rintro ⟨-, g, hg, hw⟩
    exact memSobolev_of_hasWeakGradient hf hg hw
  · intro h
    obtain ⟨g, hg, hw⟩ := exists_weakGradient_of_memSobolev hf h
    exact ⟨hf, g, hg, hw⟩

/-! ### The norm identity -/

/-- Auxiliary: if `c · (h T_U) = T_V` as tempered distributions, with `U, V ∈ L²` and `h` of
temperate growth, then `V = c h U` almost everywhere. -/
theorem ae_eq_of_smulLeft {U V : Lp ℂ 2 (volume : Measure (Rd d))} {h : Rd d → ℂ}
    (hh : h.HasTemperateGrowth) (c : ℂ)
    (hUV : c • smulLeftCLM ℂ h (U : 𝓢'(Rd d, ℂ)) = (V : 𝓢'(Rd d, ℂ))) :
    (V : Rd d → ℂ) =ᵐ[volume] fun x => c * h x * U x := by
  have hU : LocallyIntegrable (U : Rd d → ℂ) volume :=
    (Lp.memLp U).locallyIntegrable (by norm_num)
  have hV : LocallyIntegrable (V : Rd d → ℂ) volume :=
    (Lp.memLp V).locallyIntegrable (by norm_num)
  have hhU : LocallyIntegrable (fun x => c * h x * U x) volume :=
    hU.continuous_mul (continuous_const.mul hh.1.continuous)
  have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hV.sub hhU) fun φ hφ hφc => by
    have hT : IsTestFunction φ := ⟨hφ, hφc⟩
    have e := congrArg (fun T : 𝓢'(Rd d, ℂ) => T (testSchwartz hT)) hUV
    simp only [smul_apply, smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply hh,
      testSchwartz_apply, smul_eq_mul] at e
    have i1 : Integrable (fun x => φ x • (V x : ℂ)) volume :=
      hV.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have i2 : Integrable (fun x => φ x • (c * h x * U x)) volume :=
      hhU.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub i1 i2]
    have e1 : ∫ x, φ x • (V x : ℂ) = ∫ x, (φ x : ℂ) * V x := by
      congr 1
    have e2 : ∫ x, φ x • (c * h x * U x) = c * ∫ x, h x * (φ x : ℂ) * U x := by
      rw [← integral_const_mul]; congr 1; funext x; rw [Complex.real_smul]; ring
    rw [e1, e2, ← e, sub_self]
  filter_upwards [key] with x hx
  exact sub_eq_zero.mp hx

/-- Auxiliary: `‖F‖² = ∫ ‖F x‖²` on `L²(ℝ^d; ℂ)`. -/
theorem norm_sq_eq_integral (F : Lp ℂ 2 (volume : Measure (Rd d))) :
    ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  rw [integral_ofReal, RCLike.ofReal_re]

/-- Auxiliary to the Lean proof route: `‖F‖²` is integrable for `F ∈ L²`. -/
theorem integrable_norm_sq (F : Lp ℂ 2 (volume : Measure (Rd d))) :
    Integrable (fun x => ‖F x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)

/-- Auxiliary to the Lean proof route: `‖toL2C hf‖² = ∫ f²`. -/
theorem norm_toL2C_sq {f : Rd d → ℝ} (hf : MemLp f 2 volume) :
    ‖toL2C hf‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2C hf] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The Fourier side of the gradient: `𝓕(∂_j f) = 2πi ξ_j 𝓕 f` almost everywhere. -/
theorem fourier_grad_ae {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) (j : Fin d) :
    ((𝓕 (toL2C (memLp_inner hg (eb d j))) : Lp ℂ 2 volume) : Rd d → ℂ) =ᵐ[volume]
      fun x => (2 * π * Complex.I) * coordSym j x * (𝓕 (toL2C hf) : Lp ℂ 2 volume) x := by
  refine ae_eq_of_smulLeft (coordSym_growth j) _ ?_
  rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq]
  change _ = 𝓕 (toDistr (memLp_inner hg (eb d j)))
  rw [← lineDeriv_toDistr hf hg hw, fourier_lineDerivOp_eq]
  rfl

/-- The Fourier side of the Bessel potential: `𝓕 W = ⟨ξ⟩ 𝓕 f` almost everywhere. -/
theorem fourier_bessel_ae {f : Rd d → ℝ} (hf : MemLp f 2 volume)
    (W : Lp ℂ 2 (volume : Measure (Rd d)))
    (hW : besselPotential (Rd d) ℂ 1 (toDistr hf) = (W : 𝓢'(Rd d, ℂ))) :
    ((𝓕 W : Lp ℂ 2 volume) : Rd d → ℂ) =ᵐ[volume]
      fun x => 1 * besSym d 1 x * (𝓕 (toL2C hf) : Lp ℂ 2 volume) x := by
  refine ae_eq_of_smulLeft (besSym_growth 1) 1 ?_
  rw [one_smul, ← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq,
    ← hW, fourier_besselPotential_eq_smulLeftCLM_fourier_apply]
  rfl

/-- Auxiliary to the Lean proof route: `|⟨ξ⟩|² = 1 + ‖ξ‖²`. -/
theorem norm_besSym_one_sq (x : Rd d) : ‖besSym d 1 x‖ ^ 2 = 1 + ‖x‖ ^ 2 := by
  have hpos : 0 ≤ 1 + ‖x‖ ^ 2 := by positivity
  rw [besSym, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    show ((1 : ℝ) / 2) = 1 / 2 from rfl, ← Real.sqrt_eq_rpow, Real.sq_sqrt hpos]

/-- Auxiliary to the Lean proof route: the pointwise Plancherel bookkeeping
`‖⟨ξ⟩ b‖² = ‖b‖² + (2π)⁻² Σ_j ‖2πi ξ_j b‖²`. -/
theorem pointwise_sq {a b : ℂ} {c : Fin d → ℂ} {x : Rd d} (ha : a = 1 * besSym d 1 x * b)
    (hc : ∀ j, c j = 2 * π * Complex.I * coordSym j x * b) :
    ‖a‖ ^ 2 = ‖b‖ ^ 2 + ∑ j, ((2 * π) ^ 2)⁻¹ * ‖c j‖ ^ 2 := by
  have hpi : (0 : ℝ) < (2 * π) ^ 2 := by positivity
  have h2 : ‖(2 * π * Complex.I : ℂ)‖ ^ 2 = (2 * π) ^ 2 := by
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hcoord : ∀ j, ‖coordSym j x‖ ^ 2 = inner ℝ x (eb d j) ^ 2 := fun j => by
    simp [coordSym, sq_abs]
  have e : ∀ j, ((2 * π) ^ 2)⁻¹ * ‖c j‖ ^ 2 = inner ℝ x (eb d j) ^ 2 * ‖b‖ ^ 2 := fun j => by
    rw [hc j, norm_mul, norm_mul]
    have : (‖(2 * π * Complex.I : ℂ)‖ * ‖coordSym j x‖ * ‖b‖) ^ 2 =
        ‖(2 * π * Complex.I : ℂ)‖ ^ 2 * ‖coordSym j x‖ ^ 2 * ‖b‖ ^ 2 := by ring
    rw [this, h2, hcoord]
    field_simp
  rw [ha, norm_mul, norm_mul, mul_pow, mul_pow, norm_one, one_pow, one_mul,
    norm_besSym_one_sq]
  simp only [e]
  rw [← Finset.sum_mul, sum_sq_coord]
  ring

/-- **Norm identity (Mathlib's convention).** If `g ∈ L²` is a weak gradient of the real
`f ∈ L²` and `W ∈ L²` represents `J¹ T_f`, then `‖W‖² = ‖f‖₂² + (2π)⁻² ‖g‖₂²`. -/
theorem norm_sq_of_besselPotential_eq {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hw : HasWeakGradient f g)
    (W : Lp ℂ 2 (volume : Measure (Rd d)))
    (hW : besselPotential (Rd d) ℂ 1 (toDistr hf) = (W : 𝓢'(Rd d, ℂ))) :
    ‖W‖ ^ 2 = (∫ x, f x ^ 2) + ((2 * π) ^ 2)⁻¹ * ∫ x, ‖g x‖ ^ 2 := by
  set Uh : Lp ℂ 2 (volume : Measure (Rd d)) := 𝓕 (toL2C hf)
  set Gh : Fin d → Lp ℂ 2 (volume : Measure (Rd d)) :=
    fun j => 𝓕 (toL2C (memLp_inner hg (eb d j)))
  have hpi : (0 : ℝ) < (2 * π) ^ 2 := by positivity
  -- pointwise: ‖𝓕W‖² = ‖Uh‖² + (2π)⁻² Σ ‖Gh_j‖²
  have hae : (fun x => ‖(𝓕 W : Lp ℂ 2 volume) x‖ ^ 2) =ᵐ[volume]
      fun x => ‖Uh x‖ ^ 2 + ∑ j, ((2 * π) ^ 2)⁻¹ * ‖Gh j x‖ ^ 2 := by
    have hG := ae_all_iff.mpr fun j => fourier_grad_ae hf hg hw j
    filter_upwards [fourier_bessel_ae hf W hW, hG] with x hx hGx
    exact pointwise_sq hx hGx
  have i0 := integrable_norm_sq Uh
  have iG : ∀ j ∈ Finset.univ, Integrable (fun x => ((2 * π) ^ 2)⁻¹ * ‖Gh j x‖ ^ 2) volume :=
    fun j _ => (integrable_norm_sq (Gh j)).const_mul _
  rw [← Lp.norm_fourier_eq W, norm_sq_eq_integral, integral_congr_ae hae,
    integral_add i0 (integrable_finsetSum Finset.univ iG), integral_finsetSum _ iG]
  simp_rw [integral_const_mul]
  have hsum : ∫ x, ‖g x‖ ^ 2 = ∑ j, ∫ x, inner ℝ (g x) (eb d j) ^ 2 := by
    rw [← integral_finsetSum _ fun j _ => (memLp_inner hg (eb d j)).integrable_sq]
    congr 1; funext x; rw [sum_sq_coord]
  have ht : ∀ j, ∫ x, ‖(Gh j : Rd d → ℂ) x‖ ^ 2 = ∫ x, inner ℝ (g x) (eb d j) ^ 2 := fun j => by
    rw [← norm_sq_eq_integral, Lp.norm_fourier_eq, norm_toL2C_sq]
  rw [← norm_sq_eq_integral, Lp.norm_fourier_eq, norm_toL2C_sq, hsum]
  simp only [ht, Finset.mul_sum]

/-! ### The bundled element of `H^{1}` and density -/

open scoped BesselPotentialSpace

/-- The element of Mathlib's bundled `H^1 = H^{1,2}(ℝ^d; ℂ)` defined by a real `f ∈ H^1`. -/
def toH1 {f : Rd d → ℝ} (h : MemH1 f) : H^{1}(Rd d) :=
  ((memH1_iff_memSobolev h.1).mp h).toBesselPotentialSpace

/-- The distribution underlying `toH1 h` is `T_f`. -/
@[simp]
theorem toH1_toDistr {f : Rd d → ℝ} (h : MemH1 f) : (toH1 h).toDistr = toDistr h.1 :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- **Norm identity for the bundled element (Mathlib's `2π` convention).** -/
theorem norm_toH1_sq {f : Rd d → ℝ} (h : MemH1 f) {g : Rd d → Rd d}
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) :
    ‖toH1 h‖ ^ 2 = (∫ x, f x ^ 2) + ((2 * π) ^ 2)⁻¹ * ∫ x, ‖g x‖ ^ 2 := by
  have hB := (toH1 h).bessel_toDistr_eq_toLp
  rw [toH1_toDistr] at hB
  rw [← BesselPotentialSpace.norm_toLp_eq]
  exact norm_sq_of_besselPotential_eq h.1 hg hw _ hB

/-- The manuscript's `H^1` norm squared, `‖f‖₂² + ‖∇f‖₂²` (no `2π` factor; it is the norm of
`notes/integrated_signed_static.tex`, `P:signed-closed-form`). -/
def manuscriptH1NormSq (f : Rd d → ℝ) (g : Rd d → Rd d) : ℝ :=
  (∫ x, f x ^ 2) + ∫ x, ‖g x‖ ^ 2

/-- The two norms are equivalent: `‖·‖²_Mathlib ≤ ‖·‖²_ms ≤ (2π)² ‖·‖²_Mathlib`. -/
theorem norm_toH1_sq_le_manuscript {f : Rd d → ℝ} (h : MemH1 f) {g : Rd d → Rd d}
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) :
    ‖toH1 h‖ ^ 2 ≤ manuscriptH1NormSq f g ∧
      manuscriptH1NormSq f g ≤ (2 * π) ^ 2 * ‖toH1 h‖ ^ 2 := by
  rw [norm_toH1_sq h hg hw, manuscriptH1NormSq]
  have hA : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hpi : 1 ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hinv : ((2 * π) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
  have hpos : (0 : ℝ) < (2 * π) ^ 2 := by positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hinv hB]
  · rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    nlinarith

/-- A test function lies in `H^1` (its classical gradient is a weak gradient). -/
theorem memH1_of_test {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : MemH1 φ :=
  ⟨VariationalFloor.memLp_test hφ, grad φ, VariationalFloor.memLp_grad hφ,
    VariationalFloor.hasWeakGradient_of_test hφ⟩

/-- Weak gradients of `L²` pairs subtract. -/
theorem hasWeakGradient_sub {f₁ f₂ : Rd d → ℝ} {g₁ g₂ : Rd d → Rd d}
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) (hg₁ : MemLp g₁ 2 volume)
    (hg₂ : MemLp g₂ 2 volume) (hw₁ : HasWeakGradient f₁ g₁) (hw₂ : HasWeakGradient f₂ g₂) :
    HasWeakGradient (f₁ - f₂) (g₁ - g₂) := by
  intro φ hφ v
  have m := memLp_fderiv_apply (VariationalFloor.memLp_grad hφ) v
  have i1 : Integrable (fun x => f₁ x * fderiv ℝ φ x v) volume := hf₁.integrable_mul m
  have i2 : Integrable (fun x => f₂ x * fderiv ℝ φ x v) volume := hf₂.integrable_mul m
  have j1 : Integrable (fun x => inner ℝ (g₁ x) v * φ x) volume :=
    (memLp_inner hg₁ v).integrable_mul (VariationalFloor.memLp_test hφ)
  have j2 : Integrable (fun x => inner ℝ (g₂ x) v * φ x) volume :=
    (memLp_inner hg₂ v).integrable_mul (VariationalFloor.memLp_test hφ)
  have e1 : ∫ x, (f₁ - f₂) x * fderiv ℝ φ x v =
      (∫ x, f₁ x * fderiv ℝ φ x v) - ∫ x, f₂ x * fderiv ℝ φ x v := by
    rw [← integral_sub i1 i2]; congr 1; funext x; simp only [Pi.sub_apply]; ring
  have e2 : ∫ x, inner ℝ ((g₁ - g₂) x) v * φ x =
      (∫ x, inner ℝ (g₁ x) v * φ x) - ∫ x, inner ℝ (g₂ x) v * φ x := by
    rw [← integral_sub j1 j2]; congr 1; funext x; simp only [Pi.sub_apply, inner_sub_left]; ring
  rw [e1, e2]
  linarith [hw₁ φ hφ v, hw₂ φ hφ v]

/-- Auxiliary to the Lean proof route: complexification commutes with subtraction. -/
theorem toL2C_sub {f₁ f₂ : Rd d → ℝ} (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) :
    toL2C (hf₁.sub hf₂) = toL2C hf₁ - toL2C hf₂ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2C (hf₁.sub hf₂), coeFn_toL2C hf₁, coeFn_toL2C hf₂,
    Lp.coeFn_sub (toL2C hf₁) (toL2C hf₂)] with x h0 h1 h2 h3
  rw [h0, h3]
  simp only [Pi.sub_apply]
  rw [h1, h2, Complex.ofReal_sub]

/-- Auxiliary to the Lean proof route: `T_{f₁ - f₂} = T_{f₁} - T_{f₂}`. -/
theorem toDistr_sub {f₁ f₂ : Rd d → ℝ} (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) :
    toDistr (hf₁.sub hf₂) = toDistr hf₁ - toDistr hf₂ := by
  change Lp.toTemperedDistributionCLM ℂ volume 2 (toL2C (hf₁.sub hf₂)) =
    Lp.toTemperedDistributionCLM ℂ volume 2 (toL2C hf₁) -
      Lp.toTemperedDistributionCLM ℂ volume 2 (toL2C hf₂)
  rw [toL2C_sub, map_sub]

/-- Auxiliary: `∫ ‖u‖² = ((eLpNorm u 2).toReal)²` for `u ∈ L²` with values in a real
inner-product space. -/
theorem integral_norm_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : Rd d → E} (hu : MemLp u 2 volume) :
    ∫ x, ‖u x‖ ^ 2 = (eLpNorm u 2 volume).toReal ^ 2 := by
  rw [← Lp.norm_toLp u hu, @norm_sq_eq_re_inner ℝ, MeasureTheory.L2.inner_def]
  simp only [RCLike.re_to_real, real_inner_self_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx]

/-- Auxiliary to the Lean proof route: `a_n → 0` in `ℝ≥0∞` gives `(a_n).toReal² → 0`. -/
theorem tendsto_sq_toReal {a : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => (a n).toReal ^ 2) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ha
  simpa using h.pow 2

/-- **Density of real `C_c^∞` in Mathlib's `H^1`** (for the real profiles of the
manuscript): every real `f ∈ H^1` is the `H^{1}(ℝ^d)`-limit of test functions. -/
theorem exists_test_tendsto_toH1 {f : Rd d → ℝ} (h : MemH1 f) :
    ∃ φ : ℕ → Rd d → ℝ, ∃ hφ : ∀ n, IsTestFunction (φ n),
      Tendsto (fun n => toH1 (memH1_of_test (hφ n))) atTop (𝓝 (toH1 h)) := by
  obtain ⟨g, hg, hw, φ, hφ, h1, h2⟩ := H1Density.h1TestDense_of_memH1 h
  refine ⟨φ, hφ, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hsq : ∀ n, ‖toH1 (memH1_of_test (hφ n)) - toH1 h‖ ^ 2 =
      (eLpNorm (fun x => φ n x - f x) 2 volume).toReal ^ 2 + ((2 * π) ^ 2)⁻¹ *
        (eLpNorm (fun x => grad (φ n) x - g x) 2 volume).toReal ^ 2 := by
    intro n
    have hL := (VariationalFloor.memLp_test (hφ n)).sub h.1
    have hG := (VariationalFloor.memLp_grad (hφ n)).sub hg
    have hW := hasWeakGradient_sub (VariationalFloor.memLp_test (hφ n)) h.1
      (VariationalFloor.memLp_grad (hφ n)) hg (VariationalFloor.hasWeakGradient_of_test (hφ n)) hw
    rw [← BesselPotentialSpace.norm_toLp_eq, BesselPotentialSpace.toLp_sub,
      norm_sq_of_besselPotential_eq hL hG hW]
    · have a1 := integral_norm_sq_eq hL
      simp only [Real.norm_eq_abs, sq_abs] at a1
      rw [a1, integral_norm_sq_eq hG]
      rfl
    · rw [toDistr_sub (VariationalFloor.memLp_test (hφ n)) h.1, map_sub,
        ← toH1_toDistr (memH1_of_test (hφ n)), ← toH1_toDistr h,
        BesselPotentialSpace.bessel_toDistr_eq_toLp, BesselPotentialSpace.bessel_toDistr_eq_toLp,
        ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply,
        ← Lp.toTemperedDistributionCLM_apply, map_sub]
  have hT : Tendsto (fun n => ‖toH1 (memH1_of_test (hφ n)) - toH1 h‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hsq]
    simpa using (tendsto_sq_toReal h1).add ((tendsto_sq_toReal h2).const_mul ((2 * π) ^ 2)⁻¹)
  have := (Real.continuous_sqrt.tendsto 0).comp hT
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

/-- **Density of Schwartz functions in Mathlib's `H^s`** (every `s`, complex-valued): every
`u ∈ H^{s}(ℝ^d)` is a limit of elements whose distributions are Schwartz functions. -/
theorem exists_schwartz_tendsto (s : ℝ) (u : H^{s}(Rd d)) :
    ∃ φ : ℕ → H^{s}(Rd d), (∀ n, ∃ χ : 𝓢(Rd d, ℂ), (φ n).toDistr = (χ : 𝓢'(Rd d, ℂ))) ∧
      Tendsto φ atTop (𝓝 u) := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := Rd d) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top
  obtain ⟨x, hx, hxT⟩ := mem_closure_iff_seq_limit.mp (hd u.toLp)
  choose ψ hψ using hx
  have hg : (fun ξ : Rd d => (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  let χ : ℕ → 𝓢(Rd d, ℂ) := fun n => SchwartzMap.fourierMultiplierCLM ℂ
    (fun ξ : Rd d => (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) (ψ n)
  have hB : ∀ n, besselPotential (Rd d) ℂ s (χ n : 𝓢'(Rd d, ℂ)) = (x n : 𝓢'(Rd d, ℂ)) := by
    intro n
    rw [← fourierMultiplierCLM_toTemperedDistributionCLM_eq hg]
    change besselPotential (Rd d) ℂ s (besselPotential (Rd d) ℂ (-s) (ψ n : 𝓢'(Rd d, ℂ))) = _
    rw [besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero,
      ContinuousLinearMap.id_apply, ← hψ n]
    simp [Lp.toTemperedDistribution_toLp_eq]
  refine ⟨fun n => ⟨(χ n : 𝓢'(Rd d, ℂ)), x n, hB n⟩, fun n => ⟨χ n, rfl⟩,
    tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have := tendsto_iff_norm_sub_tendsto_zero.mp hxT
  refine this.congr fun n => ?_
  rw [← BesselPotentialSpace.norm_toLp_eq, BesselPotentialSpace.toLp_sub]

/-- A nonzero test function on `ℝ^d`, `d ≥ 1`, has positive gradient energy
`∫ ‖∇φ‖² > 0`. -/
theorem integral_norm_grad_sq_pos {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (hd : 0 < d)
    (hne : ∃ x, φ x ≠ 0) : 0 < ∫ x, ‖grad φ x‖ ^ 2 := by
  have : Nontrivial (Rd d) :=
    ⟨⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), 0, by simp⟩⟩
  have hc : Continuous fun x => ‖grad φ x‖ ^ 2 :=
    (VariationalFloor.continuous_grad hφ).norm.pow 2
  have hint : Integrable (fun x => ‖grad φ x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm
      (VariationalFloor.memLp_grad hφ).aestronglyMeasurable).mp (VariationalFloor.memLp_grad hφ)
  refine lt_of_le_of_ne (integral_nonneg fun x => by positivity) fun h0 => ?_
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint).mp h0.symm
  have hall : (fun x => ‖grad φ x‖ ^ 2) = fun _ => (0 : ℝ) :=
    (hc.ae_eq_iff_eq volume continuous_const).mp hae
  have hfd : ∀ x, fderiv ℝ φ x = 0 := fun x => by
    have := congrFun hall x
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero, grad] at this
    simpa using this
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ : ∃ y, y ∉ tsupport φ := by
    by_contra hcon
    push Not at hcon
    exact hφ.2.isCompact.ne_univ (Set.eq_univ_of_forall hcon)
  exact hx ((is_const_of_fderiv_eq_zero (hφ.1.differentiable (by simp)) hfd x y).trans
    (image_eq_zero_of_notMem_tsupport hy))

/-! ### The wrapper with the manuscript's hypotheses -/

/-- **K5a, manuscript form.** For a real square-integrable `f` on `ℝ^d` (the class of the main
TeX lines 748-750 at 39f2597a):
1. `f ∈ H^1(ℝ^d; ℝ)` in the manuscript's weak-gradient sense iff its distribution lies in
   Mathlib's `H^{1,2}(ℝ^d; ℂ)`;
2. for `f ∈ H^1` with weak gradient `g`, Mathlib's norm is
   `‖f‖²_{H^{1}} = ‖f‖₂² + (2π)⁻² ‖g‖₂²`, and the manuscript norm `‖f‖₂² + ‖g‖₂²`
   (`notes/integrated_signed_static.tex`, line 85) lies between `‖f‖²_{H^{1}}` and
   `(2π)² ‖f‖²_{H^{1}}`;
3. real test functions converge to `f` in Mathlib's `H^{1}` norm
   (`notes/integrated_spatial_occupation.tex`, lines 352-356). -/
theorem h1_identification_paper {f : Rd d → ℝ} (hf : MemLp f 2 volume) :
    (MemH1 f ↔ MemSobolev 1 2 (toDistr hf)) ∧
    ∀ h : MemH1 f,
      (∀ g : Rd d → Rd d, MemLp g 2 volume → HasWeakGradient f g →
        ‖toH1 h‖ ^ 2 = (∫ x, f x ^ 2) + ((2 * π) ^ 2)⁻¹ * ∫ x, ‖g x‖ ^ 2 ∧
        ‖toH1 h‖ ^ 2 ≤ manuscriptH1NormSq f g ∧
        manuscriptH1NormSq f g ≤ (2 * π) ^ 2 * ‖toH1 h‖ ^ 2) ∧
      ∃ φ : ℕ → Rd d → ℝ, ∃ hφ : ∀ n, IsTestFunction (φ n),
        Tendsto (fun n => toH1 (memH1_of_test (hφ n))) atTop (𝓝 (toH1 h)) :=
  ⟨memH1_iff_memSobolev hf, fun h =>
    ⟨fun _ hg hw => ⟨norm_toH1_sq h hg hw, norm_toH1_sq_le_manuscript h hg hw⟩,
      exists_test_tendsto_toH1 h⟩⟩

end StratonovichHAMSecondMoment.H1Mathlib
