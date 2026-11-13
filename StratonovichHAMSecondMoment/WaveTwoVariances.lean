module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Proposition `P:wave-two-variances` (Both variance directions) of
`notes/integrated_wave_variance.tex` at revision a284420: statement TeX lines 368-383
(displays `E:wave-input-variance` 374-376 and `E:wave-output-variance` 377-379), proof
lines 385-460 (displays `E:variance-kernel-time-bound` 390-393 and
`E:variance-actual-row-bound` 398-401). Also used: the section's standing assumptions
(lines 4-20: `H:homog`, `a = α₀`, `E:variance-gamma-range`, `B_α(h)`), the kernel
`E:variance-normalized-kernel` (229-238), the right side of
`E:variance-normalized-covariance` (240-246), the mask `ζ` and the interval `I`
(185-188), `C_ν` (`E:variance-actual-growth-constant`, 205-208), `J` (171-176) and
`E:variance-beta-range` (143-146).

What is formalized.
1. The purely spectral core, with NO supplied input (`wave_two_variances`, general
   form): for any measure `ν` on `ℝ^d` with `ν(B(y,r)) ≤ C r^α`, any finite
   `L²(ℝ^d; ℂ²)`-orthonormal family `U_k` (standing for `J e_k`) and `V ∈ L²(ℝ^d; ℂ²)`
   (standing for `J z`):
   `∑_k ∫ ‖∫ ∑_{ij} 1_I 𝒦_ij(·;η+λ,η) U_kj(η) conj V_i(η+λ) dη‖²_{H_a} ν(dλ)
    ≤ 4 A_T K C h^{2-a} B_α(h) ‖⟨ξ⟩^{-γ} V‖₂²` (`InputBound`), and for even `ν` the
   output version with `U = J z` fixed and `V_k = J e_k` orthonormal (`OutputBound`).
   `H_a` is the concrete completion `TimeCompletion.Ha p` (`L:masked-time-completion`)
   and `1_I 𝒦_ij(·; ξ, η)` is its element `kerH` (the class of the masked kernel under
   `TimeCompletion.extL2`). `K` is the constant of `P:frequency-row`, `A_T = C₁(a)(1+T)⁴`.
   The `h^{2β}` form is `wave_two_variances_beta`.
2. The same for the manuscript's `ν_R` (`MaskedAuxiliaryNorm.nu μ ζ R`) under the
   section's hypotheses (`wave_two_variances_core_paper`, `..._core_beta_paper`), with
   `C_T = 4 A_T K C_ν` (TeX line 432), uniform in `R`, `I` and the family.
3. `wave_two_variances_paper`: the proposition itself, with two named inputs (below).

Supplied inputs (named hypotheses of `wave_two_variances_paper` only; the core has none).
* `hlink`: `E:variance-normalized-covariance` (TeX lines 240-246), the last claim of
  `P:actual-wave-form` (B22). `ℓ_R` needs the noise `W` (D1), which this package does not
  construct; the input bounds the abstract number `var R t₀ h z w` (standing for
  `E|ℓ_R([t₀,t₀+h]; z, w)|²`) by the lower integral `∫ ‖coef p t₀ h (Jz) (Jw) λ‖² ν_R(dλ)`,
  exactly the TeX's display with `U = Jz`, `V = Jw` (the TeX integral is of a nonnegative
  function, lines 410-411). No stronger than its source.
* `hJL2`, `hJ`, `hnormSG` (D8, TeX lines 171-176 and 431): `J` maps the Schwartz phases
  into `L²(ℝ^d; ℂ²)` preserving inner products (the TeX's `J` is unitary onto
  `L²(ℝ^d; ℂ²)`; only isometry is used), and `‖z‖²_{E_{s-γ}} = ‖⟨ξ⟩^{-γ} J z‖₂²`.
  The phases are an abstract complex inner product space `P`.

Narrower than the TeX. `wave_two_variances_paper` is about the abstract `var` linked to
`ℓ_R` by `hlink`, not about `E|ℓ_R|²` itself; `ℓ_R`, the Sobolev spaces `E_r` and the
unitarity of `J` are not constructed. The family is orthonormal in `P` (the TeX's
"`E`-orthonormal Schwartz family"). The core results are not narrower: they are the
TeX's proof (lines 385-458) with `ν_R` generalized to any measure with the growth bound.

Implicit hypotheses made explicit. `U, V ∈ L²(ℝ^d; ℂ²)` componentwise (`MemLp 2`); the
family is orthonormal in the sense of `PhaseBessel.IsOrthonormalL2`; Bochner
integrability of every spatial `H_a`-valued integrand is part of the conclusion (so the
inner integral is never Lean's junk `0`); the `λ` integrals are lower integrals of
nonnegative functions (as in the TeX, lines 410-411), and the right sides are real
Bochner integrals whose integrability is part of the conclusion; `γ ≥ 0` in the general
form (the TeX has `γ > 0`). In the general form `ν` needs no evenness except for the
output direction, and no local finiteness or density (both follow, or are not needed:
local finiteness follows from the growth bound, `isLocallyFinite_of_growth`).

Hypotheses carried but unused. In the wrappers: the mask properties of `ζ` (even,
nonnegative, `1` on `B_1`, `0` off `B_2`; growth and evenness of `ν_R` hold for every real
Schwartz `ζ`), `1/2 < β`, and the fields of `H:homog` other than `μ_radon` (for
s-finiteness), `μ_tempered`, `μ_even`, `spectral`, `scaling`, `alpha0_lt_one`,
`threshold`. `Γ ≠ 0` is not assumed (the TeX treats `Γ = 0` separately, line 202; here
`ν_R = 0` is covered by the same argument).

Proof route (differences from the TeX).
* Strong measurability of `(ξ, η) ↦ 1_I 𝒦_ij(·; ξ, η) ∈ H_a` (TeX lines 404-408) is
  proved by continuity (`continuous_kerH`): the entries are jointly continuous in
  `((ξ,η), t)` (with `b_r(t) = ⟨r⟩ t sinc(rt)`), hence uniformly continuous on compact
  sets (Heine-Cantor), hence continuous into `L²(0,T)`, and `extL2` is continuous. The
  fallback of the wave plan (this measurability as a named input) was NOT needed.
* `E:variance-kernel-time-bound` is `masked_continuous_wave_completed_paper` divided by
  `⟨ξ⟩⟨η⟩` (`norm_kerH_sq_le`), as in the TeX.
* The `λ` integral is done with lower integrals and Tonelli (`total_of_fixed`); no
  measurability of `λ ↦ ∫ … dη` is needed (superadditivity of the lower integral), and
  the TeX's `λ` integrals are of nonnegative functions too. The row bound
  `E:variance-actual-row-bound` is the integral clause of `FrequencyRow.frequency_row`.
* The `h^{2β}` forms use the time-scale step `FrequencyRow.scale_time_le` of
  `C:frequency-time` (same inequality as the TeX's use of the corollary).
Declarations whose doc string says "Auxiliary" serve only this Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TimeCompletion
public import StratonovichHAMSecondMoment.PhaseBessel
public import StratonovichHAMSecondMoment.FrequencyRow
public import StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted
public import StratonovichHAMSecondMoment.MaskedAuxiliaryNorm

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ENNReal

namespace StratonovichHAMSecondMoment.WaveTwoVariances

open StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.MaskedTrigProducts (bracket frequencyPair)
open StratonovichHAMSecondMoment.MaskedContinuousWave (Wave cFn bFn waveFn C₁)
open StratonovichHAMSecondMoment.TimeCompletion
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)
open StratonovichHAMSecondMoment.FrequencyRow (rowKernel)

/-- Auxiliary (Lean proof route): `b_r(t) = ⟨r⟩ · t · sinc(rt)` for every real `r, t`
(the continuous sine quotient of TeX lines 185, 250-251, 326-327), used for joint
continuity in `(r, t)`. -/
theorem bFn_eq_sinc (r t : ℝ) : bFn r t = bracket r * (t * Real.sinc (r * t)) := by
  by_cases hr : r = 0
  · simp [bFn, hr, bracket]
  · by_cases ht : t = 0
    · simp [bFn, hr, ht]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hr ht)]
      simp only [bFn, hr, ite_false]
      field_simp

/-- Auxiliary (Lean proof route): `(r, t) ↦ b_r(t)` is jointly continuous. -/
theorem continuous_bFn : Continuous fun x : ℝ × ℝ => bFn x.1 x.2 := by
  simp_rw [bFn_eq_sinc]
  have := FrequencyRow.continuous_bracket
  fun_prop


/-- The row factor of `E:variance-normalized-kernel` (TeX lines 231-238): `b_r` in row
`i = 0` (the TeX's row 1) and `c_r` in row `i = 1` (row 2). -/
def rowWave : Fin 2 → Wave := ![.b, .c]
/-- The row sign of `E:variance-normalized-kernel`: `-1` in row `0`, `+1` in row `1`. -/
def rowSign : Fin 2 → ℝ := ![-1, 1]
/-- The column factor of `E:variance-normalized-kernel`: `c_ρ` in column `j = 0`, `b_ρ`
in column `j = 1`. -/
def colWave : Fin 2 → Wave := ![.c, .b]

/-- The entries `𝒦_ij(t; ξ, η)` of `E:variance-normalized-kernel` (TeX lines 229-238):
`𝒦 = (⟨ξ⟩⟨η⟩)^{-1/2} [[-b_r c_ρ, -b_r b_ρ], [c_r c_ρ, c_r b_ρ]](t)` with `r = |ξ|`,
`ρ = |η|`, and `c_r, b_r` the functions of `L:masked-continuous-wave`
(`MaskedContinuousWave.cFn`, `bFn`; `b_0(t) = t`). Indices `0, 1` are the TeX's `1, 2`
(`kernelEntry_matrix`). -/
def kernelEntry {d : ℕ} (i j : Fin 2) (ξ η : Rd d) (t : ℝ) : ℝ :=
  rowSign i * ((rowWave i).eval ‖ξ‖ t * (colWave j).eval ‖η‖ t) /
    Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖)

/-- The masked kernel `t ↦ 1_I(t) 𝒦_ij(t; ξ, η)` with `I = [s, s+h]` (TeX lines 187-188,
243, 391), as a complex function. -/
def maskedKernel {d : ℕ} (s h : ℝ) (i j : Fin 2) (ξ η : Rd d) : ℝ → ℂ :=
  (Icc s (s + h)).indicator fun t => ((kernelEntry i j ξ η t : ℝ) : ℂ)

/-- Auxiliary (Lean proof route): `(r, t) ↦ F_r(t)` is jointly continuous for `F ∈ {c, b}`. -/
theorem continuous_eval (W : Wave) : Continuous fun x : ℝ × ℝ => W.eval x.1 x.2 := by
  cases W with
  | c => simp only [Wave.eval, cFn]; fun_prop
  | b => exact continuous_bFn

/-- Auxiliary (Lean proof route): `(⟨ξ⟩⟨η⟩)^{1/2} > 0`. -/
theorem sqrt_bracket_pos {d : ℕ} (ξ η : Rd d) : 0 < Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖) :=
  Real.sqrt_pos.2 (mul_pos (FrequencyRow.bracket_pos _) (FrequencyRow.bracket_pos _))

/-- Auxiliary (Lean proof route): `((ξ, η), t) ↦ 𝒦_ij(t; ξ, η)` is jointly continuous
(TeX lines 404-408: the kernels are continuous in their frequency variables). -/
theorem continuous_kernelEntry {d : ℕ} (i j : Fin 2) :
    Continuous fun x : (Rd d × Rd d) × ℝ => kernelEntry i j x.1.1 x.1.2 x.2 := by
  unfold kernelEntry
  have hb := FrequencyRow.continuous_bracket
  have h1 : Continuous fun x : (Rd d × Rd d) × ℝ => (rowWave i).eval ‖x.1.1‖ x.2 :=
    (continuous_eval _).comp ((continuous_norm.comp (continuous_fst.comp continuous_fst)).prodMk
      continuous_snd)
  have h2 : Continuous fun x : (Rd d × Rd d) × ℝ => (colWave j).eval ‖x.1.2‖ x.2 :=
    (continuous_eval _).comp ((continuous_norm.comp (continuous_snd.comp continuous_fst)).prodMk
      continuous_snd)
  refine Continuous.div (by fun_prop) (by fun_prop) fun x => (sqrt_bracket_pos _ _).ne'

/-- `1_I 𝒦_ij(·; ξ, η) ∈ L²(0,T)` for every `ξ, η` and every interval `[s, s+h]` (a
continuous function on a compact interval, extended by zero). -/
theorem memLp_maskedKernel {d : ℕ} (T s h : ℝ) (i j : Fin 2) (ξ η : Rd d) :
    MemLp (maskedKernel s h i j ξ η) 2 (volume.restrict (Icc 0 T)) := by
  have h0 : Continuous fun t : ℝ => (((ξ, η) : Rd d × Rd d), t) :=
    continuous_const.prodMk continuous_id
  have hc' : Continuous fun t : ℝ => kernelEntry i j ξ η t :=
    Continuous.congr ((continuous_kernelEntry (d := d) i j).comp h0) (fun _ => rfl)
  have hc : Continuous fun t => ((kernelEntry i j ξ η t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hc'
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := s) (b := s + h)).exists_bound_of_continuousOn
    hc.continuousOn
  unfold maskedKernel
  exact indicator_mem_L2fun T s (s + h) M (fun t => ((kernelEntry i j ξ η t : ℝ) : ℂ))
    hc.aestronglyMeasurable hM

/-- Auxiliary (Lean proof route): the class of `1_I 𝒦_ij(·; ξ, η)` in `L²(0,T)`. -/
def kernelLp {d : ℕ} (T s h : ℝ) (i j : Fin 2) (ξ η : Rd d) :
    Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) T)) :=
  (memLp_maskedKernel T s h i j ξ η).toLp _

/-- Auxiliary (Lean proof route): if `(x, t) ↦ f x t` is jointly continuous on
`(ℝ^d × ℝ^d) × ℝ`, then `x ↦ [1_S f x] ∈ L²(0,T)` is continuous (uniform convergence on
the compact `[0,T]`, Heine-Cantor, and `‖g‖_{L²} ≤ T^{1/2} sup |g|`). -/
theorem continuous_toLp_indicator {d : ℕ}
    (T : ℝ) (S : Set ℝ) (f : Rd d × Rd d → ℝ → ℂ) (hf : Continuous fun x : (Rd d × Rd d) × ℝ => f x.1 x.2)
    (hmem : ∀ x, MemLp (S.indicator (f x)) 2 (volume.restrict (Icc 0 T))) :
    Continuous fun x => (hmem x).toLp _ := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set c : ℝ := ((measureUnivNNReal (volume.restrict (Icc (0 : ℝ) T)) ^
    ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ) with hc
  have hc0 : 0 ≤ c := NNReal.coe_nonneg _
  set δ : ℝ := ε / (c + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  let g : Rd d × Rd d → Icc (0 : ℝ) T → ℂ := fun x t => f x t
  have hg : Continuous (Function.uncurry g) :=
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hU := Metric.tendstoUniformly_iff.1 (hg.tendstoUniformly g x0) δ hδ0
  filter_upwards [hU] with x hx
  rw [dist_eq_norm, ← MemLp.toLp_sub]
  have hb : ‖MemLp.toLp _ ((hmem x).sub (hmem x0))‖ ≤ c * δ := by
    refine Lp.norm_le_of_ae_bound hδ0.le ?_
    filter_upwards [MemLp.coeFn_toLp ((hmem x).sub (hmem x0)),
      ae_restrict_mem measurableSet_Icc] with t ht htT
    rw [ht, Pi.sub_apply]
    have hle : ‖S.indicator (f x) t - S.indicator (f x0) t‖ ≤ ‖f x t - f x0 t‖ := by
      by_cases hS : t ∈ S <;> simp [hS]
    refine hle.trans ?_
    have := hx ⟨t, htT⟩
    rw [dist_comm, dist_eq_norm] at this
    exact this.le
  refine lt_of_le_of_lt hb ?_
  rw [hδ, mul_div_assoc', div_lt_iff₀ (by linarith)]
  nlinarith


/-- The element `1_I 𝒦_ij(·; ξ, η)` of the temporal completion `H_a = TimeCompletion.Ha p`
(the TeX's `H_a^ℂ`, TeX lines 243, 391), defined as the image of its `L²(0,T)` class
under the continuous inclusion `TimeCompletion.extL2` (TeX lines 148-149). -/
def kerH (p : TimeParams) {d : ℕ} (s h : ℝ) (i j : Fin 2) (ξ η : Rd d) : Ha p :=
  extL2 p (kernelLp p.T s h i j ξ η)

/-- Auxiliary (Lean proof route): `(ξ, η) ↦ [1_I 𝒦_ij(·; ξ, η)] ∈ L²(0,T)` is continuous. -/
theorem continuous_kernelLp {d : ℕ} (T s h : ℝ) (i j : Fin 2) :
    Continuous fun x : Rd d × Rd d => kernelLp T s h i j x.1 x.2 := by
  have hf : Continuous fun x : (Rd d × Rd d) × ℝ => ((kernelEntry i j x.1.1 x.1.2 x.2 : ℝ) : ℂ) :=
    Continuous.congr (Complex.continuous_ofReal.comp (continuous_kernelEntry (d := d) i j))
      (fun _ => rfl)
  exact continuous_toLp_indicator T (Icc s (s + h))
    (fun x t => ((kernelEntry i j x.1 x.2 t : ℝ) : ℂ)) hf
    (fun x => memLp_maskedKernel T s h i j x.1 x.2)

/-- The kernels are continuous into `H_a` in their frequency variables (TeX lines
407-408: "continuous into `L²(0,T)` in their frequency variables, hence into
`H_a^ℂ` by Schur"). Hence `(ξ, η) ↦ 1_I 𝒦_ij(·; ξ, η)` is strongly measurable; this is
how the "separability gives strong measurability" step (line 408) is carried out
here (continuity on a second countable space, no separability argument). -/
theorem continuous_kerH (p : TimeParams) {d : ℕ} (s h : ℝ) (i j : Fin 2) :
    Continuous fun x : Rd d × Rd d => kerH p s h i j x.1 x.2 :=
  (extL2 p).continuous.comp (continuous_kernelLp p.T s h i j)

/-- Auxiliary (Lean proof route): `1_I 𝒦_ij = (σ_i (⟨ξ⟩⟨η⟩)^{-1/2}) · 1_I F_r G_ρ` with
`F = rowWave i`, `G = colWave j` (`MaskedContinuousWave.waveFn`). -/
theorem maskedKernel_eq {d : ℕ} (s h : ℝ) (i j : Fin 2) (ξ η : Rd d) :
    maskedKernel s h i j ξ η =
      (((rowSign i / Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖) : ℝ) : ℂ)) •
        waveFn (Icc s (s + h)) (rowWave i) (colWave j) ‖ξ‖ ‖η‖ := by
  funext t
  simp only [maskedKernel, waveFn, Pi.smul_apply, smul_eq_mul]
  by_cases ht : t ∈ Icc s (s + h)
  · rw [indicator_of_mem ht, indicator_of_mem ht, kernelEntry]
    push_cast; ring
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]

/-- Auxiliary (Lean proof route): `σ_i² = 1`. -/
theorem rowSign_sq (i : Fin 2) : rowSign i ^ 2 = 1 := by
  fin_cases i <;> simp [rowSign]

/-- Auxiliary (Lean proof route): `1_I 𝒦_ij(·; ξ, η) = σ_i (⟨ξ⟩⟨η⟩)^{-1/2} · emb (1_I F_r G_ρ)`
in `H_a`. -/
theorem kerH_eq_smul_emb (p : TimeParams) {d : ℕ} (s h : ℝ) (i j : Fin 2) (ξ η : Rd d)
    (hw : waveFn (Icc s (s + h)) (rowWave i) (colWave j) ‖ξ‖ ‖η‖ ∈ L2fun p.T) :
    kerH p s h i j ξ η =
      (((rowSign i / Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖) : ℝ) : ℂ)) • emb p ⟨_, hw⟩ := by
  unfold kerH kernelLp
  have e := MemLp.toLp_const_smul
    (((rowSign i / Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖) : ℝ) : ℂ))
    (show MemLp (waveFn (Icc s (s + h)) (rowWave i) (colWave j) ‖ξ‖ ‖η‖) 2
      (volume.restrict (Icc 0 p.T)) from hw)
  simp_rw [maskedKernel_eq] at *
  rw [e, map_smul, extL2_toLp]

/-- `E:variance-kernel-time-bound` (TeX lines 386-393): for `I = [s, s+h] ⊆ [0,T]`,
`0 < h ≤ 1`, `‖1_I 𝒦_ij(·; ξ, η)‖²_{H_a} ≤ A_T h^{2-a} Φ_h(ξ, η)` with
`A_T = C₁(a)(1+T)⁴` and `Φ_h = FrequencyRow.rowKernel`, from
`MaskedContinuousWaveCompleted.masked_continuous_wave_completed_paper` divided by
`⟨ξ⟩⟨η⟩` (the sign `σ_i` has square one). -/
theorem norm_kerH_sq_le (p : TimeParams) {d : ℕ} {s h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (hsT : s + h ≤ p.T) (i j : Fin 2) (ξ η : Rd d) :
    ‖kerH p s h i j ξ η‖ ^ 2 ≤
      C₁ p.a * (1 + p.T) ^ 4 * h ^ (2 - p.a) * rowKernel p.a h ξ η := by
  obtain ⟨hw, hbd⟩ := MaskedContinuousWaveCompleted.masked_continuous_wave_completed_paper
    p.a p.T s h p.ha0 p.ha1 p.hT hh0 hh1 hs hsT ‖ξ‖ ‖η‖ (norm_nonneg _) (norm_nonneg _)
    (rowWave i) (colWave j)
  have hb := hbd hw
  have hpos : 0 < bracket ‖ξ‖ * bracket ‖η‖ :=
    mul_pos (FrequencyRow.bracket_pos _) (FrequencyRow.bracket_pos _)
  have hc2 : (rowSign i / Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖)) ^ 2 =
      1 / (bracket ‖ξ‖ * bracket ‖η‖) := by
    rw [div_pow, rowSign_sq, Real.sq_sqrt hpos.le]
  rw [kerH_eq_smul_emb p s h i j ξ η hw, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, hc2]
  have hrk : rowKernel p.a h ξ η =
      frequencyPair p.a h ‖ξ‖ ‖η‖ / (bracket ‖ξ‖ * bracket ‖η‖) := rfl
  rw [hrk]
  calc 1 / (bracket ‖ξ‖ * bracket ‖η‖) * ‖emb p ⟨_, hw⟩‖ ^ 2
      ≤ 1 / (bracket ‖ξ‖ * bracket ‖η‖) *
        (C₁ p.a * (1 + p.T) ^ 4 * h ^ (2 - p.a) * frequencyPair p.a h ‖ξ‖ ‖η‖) := by
        gcongr
    _ = _ := by ring

/-- The four entries of `E:variance-normalized-kernel` (TeX lines 233-237), written out:
`𝒦_11 = -b_r c_ρ/√(⟨ξ⟩⟨η⟩)`, `𝒦_12 = -b_r b_ρ/√·`, `𝒦_21 = c_r c_ρ/√·`, `𝒦_22 = c_r b_ρ/√·`
(Lean indices `0, 1`). -/
theorem kernelEntry_matrix {d : ℕ} (ξ η : Rd d) (t : ℝ) :
    kernelEntry 0 0 ξ η t = -(bFn ‖ξ‖ t * cFn ‖η‖ t) / Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖) ∧
    kernelEntry 0 1 ξ η t = -(bFn ‖ξ‖ t * bFn ‖η‖ t) / Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖) ∧
    kernelEntry 1 0 ξ η t = cFn ‖ξ‖ t * cFn ‖η‖ t / Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖) ∧
    kernelEntry 1 1 ξ η t = cFn ‖ξ‖ t * bFn ‖η‖ t / Real.sqrt (bracket ‖ξ‖ * bracket ‖η‖) := by
  simp [kernelEntry, rowSign, rowWave, colWave, Wave.eval]

/-- Auxiliary (Lean proof route): Cauchy-Schwarz over two components,
`‖c₀x₀ + c₁x₁‖² ≤ 2 (|c₀|²‖x₀‖² + |c₁|²‖x₁‖²)` (TeX lines 420-425). -/
theorem norm_sq_two_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : Fin 2 → ℂ) (x : Fin 2 → H) :
    ‖∑ i, c i • x i‖ ^ 2 ≤ 2 * ∑ i, ‖c i‖ ^ 2 * ‖x i‖ ^ 2 := by
  simp only [Fin.sum_univ_two]
  have h := norm_add_le (c 0 • x 0) (c 1 • x 1)
  rw [norm_smul, norm_smul] at h
  have h0 : 0 ≤ ‖c 0 • x 0 + c 1 • x 1‖ := norm_nonneg _
  have := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖c 0‖ * ‖x 0‖ - ‖c 1‖ * ‖x 1‖)]

/-- The pointwise step of TeX lines 420-428 in abstract form: if `‖k_ij‖² ≤ M` for all
`i, j ∈ {0,1}`, then `∑_j ‖∑_i c_i k_ij‖² ≤ 4 M ∑_i |c_i|²` (two-component Cauchy-Schwarz,
then the sum over the two values of `j`). -/
theorem sum_norm_sq_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : Fin 2 → ℂ) (k : Fin 2 → Fin 2 → H) (M : ℝ) (hk : ∀ i j, ‖k i j‖ ^ 2 ≤ M) :
    ∑ j, ‖∑ i, c i • k i j‖ ^ 2 ≤ 4 * M * ∑ i, ‖c i‖ ^ 2 := by
  have hj : ∀ j, ‖∑ i, c i • k i j‖ ^ 2 ≤ 2 * M * ∑ i, ‖c i‖ ^ 2 := by
    intro j
    refine (norm_sq_two_le c (fun i => k i j)).trans ?_
    calc 2 * ∑ i, ‖c i‖ ^ 2 * ‖k i j‖ ^ 2 ≤ 2 * ∑ i, M * ‖c i‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) zero_le_two
          rw [mul_comm M]
          exact mul_le_mul_of_nonneg_left (hk i j) (sq_nonneg _)
      _ = 2 * M * ∑ i, ‖c i‖ ^ 2 := by rw [← Finset.mul_sum]; ring
  calc ∑ j, ‖∑ i, c i • k i j‖ ^ 2 ≤ ∑ _j : Fin 2, 2 * M * ∑ i, ‖c i‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hj j
    _ = _ := by simp [Fin.sum_univ_two]; ring

/-- Auxiliary (Lean proof route): `Φ_h ≤ 2` for `a < 1` (used only for boundedness of the
kernels, TeX lines 405-410). -/
theorem rowKernel_le_two {d : ℕ} {a : ℝ} (ha : a < 1) (h : ℝ) (ξ η : Rd d) :
    rowKernel a h ξ η ≤ 2 := by
  unfold rowKernel
  have h1 := FrequencyRow.one_le_bracket ‖ξ‖
  have h2 := FrequencyRow.one_le_bracket ‖η‖
  rw [div_le_iff₀ (by positivity)]
  have := FrequencyRow.frequencyPair_le_two ha h ‖ξ‖ ‖η‖
  nlinarith

/-- Symmetry of `Φ_h` (used at TeX line 448: "then use symmetry of `Φ_h`"). -/
theorem rowKernel_symm {d : ℕ} (a h : ℝ) (ξ η : Rd d) : rowKernel a h ξ η = rowKernel a h η ξ := by
  unfold rowKernel frequencyPair
  rw [show h * (‖ξ‖ - ‖η‖) = -(h * (‖η‖ - ‖ξ‖)) by ring, MaskedTrigProducts.bracket_neg]
  ring_nf


/-- `A_T = C₁(a)(1+T)⁴` (TeX line 393), with `a = p.a`, `T = p.T`. -/
def AT (p : TimeParams) : ℝ := C₁ p.a * (1 + p.T) ^ 4

/-- Auxiliary (Lean proof route): `A_T ≥ 0`. -/
theorem AT_nonneg (p : TimeParams) : 0 ≤ AT p := by
  unfold AT C₁ MaskedTrigProducts.C₀
  have := sub_pos.2 p.ha1
  have := p.hT
  positivity

/-- The `H_a`-valued spatial integral inside `E:variance-normalized-covariance` (TeX lines
240-246): `∫ ∑_{i,j} 1_I 𝒦_ij(·; η+λ, η) U_j(η) conj(V_i(η+λ)) dη` with `I = [s, s+h]`,
a Bochner integral in `H_a` (its integrand's integrability is part of the conclusions
that use it). -/
def coef (p : TimeParams) {d : ℕ} (s h : ℝ) (U V : Fin 2 → Rd d → ℂ) (l : Rd d) : Ha p :=
  ∫ η, ∑ i, ∑ j, (U j η * conj (V i (η + l))) • kerH p s h i j (η + l) η

/-- Auxiliary (Lean proof route): along any continuous `η ↦ (ξ(η), η'(η))`, the kernel is
strongly measurable and essentially bounded (TeX lines 404-410). -/
theorem memLp_top_kerH (p : TimeParams) {d : ℕ} {s h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (hsT : s + h ≤ p.T) (i j : Fin 2) (f : Rd d → Rd d × Rd d) (hf : Continuous f) :
    MemLp (fun η => kerH p s h i j (f η).1 (f η).2) ∞ volume := by
  refine memLp_top_of_bound ((continuous_kerH p s h i j).comp hf).aestronglyMeasurable
    (Real.sqrt (AT p * h ^ (2 - p.a) * 2)) (ae_of_all _ fun η => ?_)
  rw [← abs_norm]
  refine Real.abs_le_sqrt ?_
  refine (norm_kerH_sq_le p hh0 hh1 hs hsT i j _ _).trans ?_
  have := rowKernel_le_two p.ha1 h (f η).1 (f η).2
  have := AT_nonneg p
  have : 0 ≤ h ^ (2 - p.a) := Real.rpow_nonneg hh0.le _
  unfold AT at *
  gcongr

/-- The input direction at fixed `λ` (TeX lines 413-432, before the `λ` integral):
for a finite `L²(ℝ^d; ℂ²)`-orthonormal family `U_k` and `V ∈ L²`, the integrands are
Bochner integrable and
`∑_k ‖∫ ∑_{ij} 1_I 𝒦_ij(·;η+λ,η) U_kj(η) conj V_i(η+λ) dη‖² ≤
 ∫ 4 A_T h^{2-a} Φ_h(ξ, ξ-λ) ∑_i |V_i(ξ)|² dξ` (lower integral; `L:phase-bessel`,
two-component Cauchy-Schwarz and the change of variables `ξ = η + λ`). -/
theorem input_fixed (p : TimeParams) {d : ℕ} {s h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (hsT : s + h ≤ p.T) {n : ℕ} (U : Fin n → Fin 2 → Rd d → ℂ)
    (hU : PhaseBessel.IsOrthonormalL2 volume U) (V : Fin 2 → Rd d → ℂ)
    (hV : ∀ i, MemLp (V i) 2 volume) (l : Rd d) :
    (∀ k, Integrable (fun η => ∑ i, ∑ j, (U k j η * conj (V i (η + l))) •
        kerH p s h i j (η + l) η)) ∧
      ENNReal.ofReal (∑ k, ‖coef p s h (U k) V l‖ ^ 2) ≤
        ∫⁻ ξ, ENNReal.ofReal (4 * AT p * h ^ (2 - p.a) * rowKernel p.a h ξ (ξ - l) *
          ∑ i, ‖V i ξ‖ ^ 2) := by
  set g : Fin 2 → Rd d → Ha p := fun j η => ∑ i, conj (V i (η + l)) • kerH p s h i j (η + l) η
    with hgdef
  have hVs : ∀ i, MemLp (fun η => conj (V i (η + l))) 2 volume := fun i =>
    PhaseBessel.memLp_conj ((hV i).comp_measurePreserving (measurePreserving_add_right volume l))
  have hcont : Continuous fun η : Rd d => (η + l, η) := by fun_prop
  have hg : ∀ j, MemLp (g j) 2 volume := by
    intro j
    have e : g j = ∑ i, (fun η => conj (V i (η + l))) •
        (fun η => kerH p s h i j (η + l, η).1 (η + l, η).2) := by
      funext η; simp [hgdef, Finset.sum_apply]
    rw [e]
    exact memLp_finsetSum' _ fun i _ =>
      MemLp.smul (hVs i) (memLp_top_kerH p hh0 hh1 hs hsT i j _ hcont)
  have heq : ∀ k, (fun η => ∑ i, ∑ j, (U k j η * conj (V i (η + l))) •
      kerH p s h i j (η + l) η) = fun η => ∑ j, U k j η • g j η := by
    intro k; funext η
    simp only [hgdef, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  obtain ⟨hint, hG, hbes⟩ := PhaseBessel.phase_bessel hU hg
  refine ⟨fun k => (heq k) ▸ hint k, ?_⟩
  have hcoef : ∀ k, coef p s h (U k) V l = PhaseBessel.coeff volume U g k := by
    intro k; unfold coef PhaseBessel.coeff; rw [heq k]
  simp_rw [hcoef]
  have hpt : ∀ η, ∑ j, ‖g j η‖ ^ 2 ≤
      4 * AT p * h ^ (2 - p.a) * rowKernel p.a h (η + l) η * ∑ i, ‖V i (η + l)‖ ^ 2 := by
    intro η
    have := sum_norm_sq_le (fun i => conj (V i (η + l))) (fun i j => kerH p s h i j (η + l) η)
      (AT p * h ^ (2 - p.a) * rowKernel p.a h (η + l) η)
      (fun i j => norm_kerH_sq_le p hh0 hh1 hs hsT i j _ _)
    simp only [RCLike.norm_conj] at this
    calc ∑ j, ‖g j η‖ ^ 2 ≤ _ := this
      _ = _ := by unfold AT; ring
  calc ENNReal.ofReal (∑ k, ‖PhaseBessel.coeff volume U g k‖ ^ 2)
      ≤ ENNReal.ofReal (∫ η, ∑ j, ‖g j η‖ ^ 2) := ENNReal.ofReal_le_ofReal hbes
    _ = ∫⁻ η, ENNReal.ofReal (∑ j, ‖g j η‖ ^ 2) :=
        ofReal_integral_eq_lintegral_ofReal hG
          (ae_of_all _ fun η => Finset.sum_nonneg fun j _ => sq_nonneg _)
    _ ≤ ∫⁻ η, ENNReal.ofReal (4 * AT p * h ^ (2 - p.a) * rowKernel p.a h (η + l) η *
          ∑ i, ‖V i (η + l)‖ ^ 2) := lintegral_mono fun η => ENNReal.ofReal_le_ofReal (hpt η)
    _ = _ := by
        have := lintegral_add_right_eq_self (μ := (volume : Measure (Rd d)))
          (fun ξ => ENNReal.ofReal (4 * AT p * h ^ (2 - p.a) * rowKernel p.a h ξ (ξ - l) *
            ∑ i, ‖V i ξ‖ ^ 2)) l
        simpa only [add_sub_cancel_right] using this

/-- The output direction at fixed `λ` (TeX lines 434-446, before the `λ` integral): for
`U ∈ L²` and a finite orthonormal family `V_k`, the integrands are Bochner integrable
and `∑_k ‖∫ ∑_{ij} 1_I 𝒦_ij(·;η+λ,η) U_j(η) conj V_ki(η+λ) dη‖² ≤
 ∫ 4 A_T h^{2-a} Φ_h(η+λ, η) ∑_j |U_j(η)|² dη` (change of variables `η = ξ - λ`, the
conjugated `L:phase-bessel`, Cauchy-Schwarz, change of variables back). -/
theorem output_fixed (p : TimeParams) {d : ℕ} {s h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (hsT : s + h ≤ p.T) (U : Fin 2 → Rd d → ℂ) (hU : ∀ j, MemLp (U j) 2 volume)
    {n : ℕ} (V : Fin n → Fin 2 → Rd d → ℂ) (hV : PhaseBessel.IsOrthonormalL2 volume V)
    (l : Rd d) :
    (∀ k, Integrable (fun η => ∑ i, ∑ j, (U j η * conj (V k i (η + l))) •
        kerH p s h i j (η + l) η)) ∧
      ENNReal.ofReal (∑ k, ‖coef p s h U (V k) l‖ ^ 2) ≤
        ∫⁻ η, ENNReal.ofReal (4 * AT p * h ^ (2 - p.a) * rowKernel p.a h (η + l) η *
          ∑ j, ‖U j η‖ ^ 2) := by
  set g : Fin 2 → Rd d → Ha p := fun i ξ => ∑ j, U j (ξ - l) • kerH p s h i j ξ (ξ - l)
    with hgdef
  have hUs : ∀ j, MemLp (fun ξ => U j (ξ - l)) 2 volume := fun j =>
    (hU j).comp_measurePreserving (measurePreserving_sub_right volume l)
  have hcont : Continuous fun ξ : Rd d => (ξ, ξ - l) := by fun_prop
  have hg : ∀ i, MemLp (g i) 2 volume := by
    intro i
    have e : g i = ∑ j, (fun ξ => U j (ξ - l)) •
        (fun ξ => kerH p s h i j (ξ, ξ - l).1 (ξ, ξ - l).2) := by
      funext ξ; simp [hgdef, Finset.sum_apply]
    rw [e]
    exact memLp_finsetSum' _ fun j _ =>
      MemLp.smul (hUs j) (memLp_top_kerH p hh0 hh1 hs hsT i j _ hcont)
  set F : Fin n → Rd d → Ha p := fun k ξ => ∑ i, conj (V k i ξ) • g i ξ with hFdef
  have heq : ∀ k, (fun η => ∑ i, ∑ j, (U j η * conj (V k i (η + l))) •
      kerH p s h i j (η + l) η) = fun η => F k (η + l) := by
    intro k; funext η
    simp only [hFdef, hgdef, Finset.smul_sum, smul_smul, add_sub_cancel_right, mul_comm]
  obtain ⟨hint, hG, hbes⟩ := PhaseBessel.phase_bessel_conj hV hg
  refine ⟨fun k => (heq k) ▸ (hint k).comp_add_right l, ?_⟩
  have hcoef : ∀ k, coef p s h U (V k) l = ∫ ξ, F k ξ := by
    intro k; unfold coef; rw [heq k]; exact integral_add_right_eq_self (F k) l
  simp_rw [hcoef]
  have hpt : ∀ ξ, ∑ i, ‖g i ξ‖ ^ 2 ≤
      4 * AT p * h ^ (2 - p.a) * rowKernel p.a h ξ (ξ - l) * ∑ j, ‖U j (ξ - l)‖ ^ 2 := by
    intro ξ
    have := sum_norm_sq_le (fun j => U j (ξ - l)) (fun j i => kerH p s h i j ξ (ξ - l))
      (AT p * h ^ (2 - p.a) * rowKernel p.a h ξ (ξ - l))
      (fun j i => norm_kerH_sq_le p hh0 hh1 hs hsT i j _ _)
    calc ∑ i, ‖g i ξ‖ ^ 2 ≤ _ := this
      _ = _ := by unfold AT; ring
  calc ENNReal.ofReal (∑ k, ‖∫ ξ, F k ξ‖ ^ 2)
      ≤ ENNReal.ofReal (∫ ξ, ∑ i, ‖g i ξ‖ ^ 2) := ENNReal.ofReal_le_ofReal hbes
    _ = ∫⁻ ξ, ENNReal.ofReal (∑ i, ‖g i ξ‖ ^ 2) :=
        ofReal_integral_eq_lintegral_ofReal hG
          (ae_of_all _ fun ξ => Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (4 * AT p * h ^ (2 - p.a) * rowKernel p.a h ξ (ξ - l) *
          ∑ j, ‖U j (ξ - l)‖ ^ 2) := lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hpt ξ)
    _ = _ := by
        have := lintegral_add_right_eq_self (μ := (volume : Measure (Rd d)))
          (fun ξ => ENNReal.ofReal (4 * AT p * h ^ (2 - p.a) * rowKernel p.a h ξ (ξ - l) *
            ∑ j, ‖U j (ξ - l)‖ ^ 2)) l
        simpa only [add_sub_cancel_right] using this.symm


/-- Auxiliary (Lean proof route): `∑_i ∫⁻ f_i ≤ ∫⁻ ∑_i f_i` for any finite family of
`[0,∞]`-valued functions (no measurability needed: superadditivity of the lower
integral). -/
theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- Auxiliary (Lean proof route): the `λ`-integration of TeX lines 429-432 (and 446-451) in
abstract form. If, for every `λ`, `∑_k ‖x_k(λ)‖² ≤ ∫ c Ψ(λ,ξ) S(ξ) dξ` (lower integral),
`Ψ` is jointly continuous, `S ≥ 0` is a.e.-measurable, the row bound
`∫ Ψ(λ,ξ) ν(dλ) ≤ R(ξ)` holds and `R S` is integrable, then
`∑_k ∫ ‖x_k(λ)‖² ν(dλ) ≤ c ∫ R S` (Tonelli). `ν` is assumed s-finite. -/
theorem total_of_fixed (p : TimeParams) {d n : ℕ} {ν : Measure (Rd d)} [SFinite ν]
    (x : Fin n → Rd d → Ha p) (S : Rd d → ℝ) (hS : AEMeasurable S volume)
    (Ψ : Rd d → Rd d → ℝ) (hΨ : Continuous fun z : Rd d × Rd d => Ψ z.1 z.2)
    (c : ℝ) (hc : 0 ≤ c) (R : Rd d → ℝ)
    (hfix : ∀ l, ENNReal.ofReal (∑ k, ‖x k l‖ ^ 2) ≤ ∫⁻ ξ, ENNReal.ofReal (c * Ψ l ξ * S ξ))
    (hrow : ∀ ξ, ∫⁻ l, ENNReal.ofReal (Ψ l ξ) ∂ν ≤ ENNReal.ofReal (R ξ))
    (hS0 : ∀ ξ, 0 ≤ S ξ) (hRS : Integrable (fun ξ => R ξ * S ξ)) (hR0 : ∀ ξ, 0 ≤ R ξ) :
    ∑ k, ∫⁻ l, ‖x k l‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (c * ∫ ξ, R ξ * S ξ) := by
  have hmeas : AEMeasurable (Function.uncurry fun l ξ => ENNReal.ofReal (c * Ψ l ξ * S ξ))
      (ν.prod volume) := by
    have h1 : AEMeasurable (fun z : Rd d × Rd d => c * Ψ z.1 z.2) (ν.prod volume) :=
      (continuous_const.mul hΨ).measurable.aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h1.mul hS.comp_snd)
  calc ∑ k, ∫⁻ l, ‖x k l‖ₑ ^ 2 ∂ν ≤ ∫⁻ l, ∑ k, ‖x k l‖ₑ ^ 2 ∂ν := sum_lintegral_le _ _
    _ = ∫⁻ l, ENNReal.ofReal (∑ k, ‖x k l‖ ^ 2) ∂ν := by
        congr 1; funext l
        rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
        simp_rw [MaskedAuxiliaryNorm.ofReal_norm_sq]
    _ ≤ ∫⁻ l, (∫⁻ ξ, ENNReal.ofReal (c * Ψ l ξ * S ξ)) ∂ν := lintegral_mono hfix
    _ = ∫⁻ ξ, ∫⁻ l, ENNReal.ofReal (c * Ψ l ξ * S ξ) ∂ν := lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (c * (R ξ * S ξ)) := by
        refine lintegral_mono fun ξ => ?_
        have e : ∀ l, ENNReal.ofReal (c * Ψ l ξ * S ξ) =
            ENNReal.ofReal (c * S ξ) * ENNReal.ofReal (Ψ l ξ) := by
          intro l
          rw [← ENNReal.ofReal_mul (mul_nonneg hc (hS0 ξ))]
          ring_nf
        simp_rw [e]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc ENNReal.ofReal (c * S ξ) * ∫⁻ l, ENNReal.ofReal (Ψ l ξ) ∂ν
            ≤ ENNReal.ofReal (c * S ξ) * ENNReal.ofReal (R ξ) := by gcongr; exact hrow ξ
          _ = _ := by rw [← ENNReal.ofReal_mul (mul_nonneg hc (hS0 ξ))]; ring_nf
    _ = ENNReal.ofReal (c * ∫ ξ, R ξ * S ξ) := by
        rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hRS.const_mul c)
          (ae_of_all _ fun ξ => mul_nonneg hc (mul_nonneg (hR0 ξ) (hS0 ξ)))]

/-- Auxiliary (Lean proof route): the growth bound `ν(B(y,r)) ≤ C r^α` with finite `C`
makes `ν` locally finite (hence σ-finite on `ℝ^d`). -/
theorem isLocallyFinite_of_growth {d : ℕ} {ν : Measure (Rd d)} {C α : ℝ}
    (hg : ∀ y : Rd d, ∀ r : ℝ, 0 < r → ν (Metric.ball y r) ≤ ENNReal.ofReal (C * r ^ α)) :
    IsLocallyFiniteMeasure ν :=
  ⟨fun y => ⟨Metric.ball y 1, Metric.ball_mem_nhds y one_pos,
    lt_of_le_of_lt (hg y 1 one_pos) ENNReal.ofReal_lt_top⟩⟩


/-- Auxiliary (Lean proof route): `Φ_h` is jointly continuous on `ℝ^d × ℝ^d`. -/
theorem continuous_rowKernel₂ {d : ℕ} (a h : ℝ) :
    Continuous fun z : Rd d × Rd d => rowKernel a h z.1 z.2 := by
  unfold rowKernel frequencyPair
  have hb := FrequencyRow.continuous_bracket
  have hr : ∀ f : Rd d × Rd d → ℝ, Continuous f → ∀ e : ℝ,
      Continuous fun z => bracket (f z) ^ e :=
    fun f hf e => (hb.comp hf).rpow_const fun z => Or.inl (FrequencyRow.bracket_pos _).ne'
  refine Continuous.div ?_ ?_ fun z => (mul_pos (FrequencyRow.bracket_pos _)
    (FrequencyRow.bracket_pos _)).ne'
  · exact (hr _ (by fun_prop) _).add (hr _ (by fun_prop) _)
  · exact (hb.comp (by fun_prop)).mul (hb.comp (by fun_prop))

/-- For `γ ≥ 0` and `V ∈ L²(ℝ^d; ℂ²)`, `ξ ↦ ⟨ξ⟩^{-2γ} ∑_i |V_i(ξ)|²` is integrable; its
integral is `‖⟨ξ⟩^{-γ} V‖₂²`, the right side of `E:wave-input-variance` after
`‖z‖_{E_{s-γ}} = ‖⟨ξ⟩^{-γ} J z‖₂` (TeX line 431). -/
theorem integrable_weight {d : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (V : Fin 2 → Rd d → ℂ)
    (hV : ∀ i, MemLp (V i) 2 volume) :
    Integrable (fun ξ : Rd d => bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ i, ‖V i ξ‖ ^ 2) := by
  have hS : Integrable (fun ξ : Rd d => ∑ i, ‖V i ξ‖ ^ 2) :=
    integrable_finsetSum _ fun i _ =>
      (memLp_two_iff_integrable_sq_norm (hV i).aestronglyMeasurable).1 (hV i)
  refine hS.bdd_mul (c := 1) ?_ (ae_of_all _ fun ξ => ?_)
  · exact ((FrequencyRow.continuous_bracket.comp continuous_norm).rpow_const
      fun ξ => Or.inl (FrequencyRow.bracket_pos _).ne').aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (FrequencyRow.bracket_pos _).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (FrequencyRow.one_le_bracket _) (by linarith)

/-- The conclusion of the input direction for a measure `ν` and a constant `M`: for every
finite `L²(ℝ^d; ℂ²)`-orthonormal family `U_k` (standing for `J e_k`) and every
`V ∈ L²(ℝ^d; ℂ²)` (standing for `J z`): every spatial integrand is Bochner integrable
in `H_a`, `⟨ξ⟩^{-2γ} ∑|V_i|²` is integrable, and
`∑_k ∫ ‖∫ ∑_{ij} 1_I 𝒦_ij(·;η+λ,η) U_kj(η) conj V_i(η+λ) dη‖²_{H_a} ν(dλ)
 ≤ M ‖⟨ξ⟩^{-γ} V‖₂²` (the `λ` integral is the lower integral of a nonnegative
function, TeX lines 410-411). -/
def InputBound (p : TimeParams) {d : ℕ} (s h : ℝ) (ν : Measure (Rd d)) (γ M : ℝ) : Prop :=
  ∀ (n : ℕ) (U : Fin n → Fin 2 → Rd d → ℂ), PhaseBessel.IsOrthonormalL2 volume U →
    ∀ V : Fin 2 → Rd d → ℂ, (∀ i, MemLp (V i) 2 volume) →
      (∀ l k, Integrable (fun η => ∑ i, ∑ j, (U k j η * conj (V i (η + l))) •
        kerH p s h i j (η + l) η)) ∧
      Integrable (fun ξ => bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ i, ‖V i ξ‖ ^ 2) ∧
      ∑ k, ∫⁻ l, ‖coef p s h (U k) V l‖ₑ ^ 2 ∂ν ≤
        ENNReal.ofReal (M * ∫ ξ, bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ i, ‖V i ξ‖ ^ 2)

/-- The conclusion of the output direction for `ν` and `M`: for every `U ∈ L²(ℝ^d; ℂ²)`
(standing for `J z`) and every finite orthonormal family `V_k` (standing for `J e_k`):
every spatial integrand is Bochner integrable, `⟨ξ⟩^{-2γ} ∑|U_j|²` is integrable, and
`∑_k ∫ ‖∫ ∑_{ij} 1_I 𝒦_ij(·;η+λ,η) U_j(η) conj V_ki(η+λ) dη‖² ν(dλ) ≤ M ‖⟨ξ⟩^{-γ} U‖₂²`. -/
def OutputBound (p : TimeParams) {d : ℕ} (s h : ℝ) (ν : Measure (Rd d)) (γ M : ℝ) : Prop :=
  ∀ U : Fin 2 → Rd d → ℂ, (∀ j, MemLp (U j) 2 volume) →
    ∀ (n : ℕ) (V : Fin n → Fin 2 → Rd d → ℂ), PhaseBessel.IsOrthonormalL2 volume V →
      (∀ l k, Integrable (fun η => ∑ i, ∑ j, (U j η * conj (V k i (η + l))) •
        kerH p s h i j (η + l) η)) ∧
      Integrable (fun ξ => bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ j, ‖U j ξ‖ ^ 2) ∧
      ∑ k, ∫⁻ l, ‖coef p s h U (V k) l‖ₑ ^ 2 ∂ν ≤
        ENNReal.ofReal (M * ∫ ξ, bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ j, ‖U j ξ‖ ^ 2)

/-- **The spectral core of `P:wave-two-variances`, no input** (TeX lines 385-451). For
`a < 1`, `α + a < 2`, `0 ≤ γ`, `2γ ≤ 1`, `α + 2γ < 2` there is `K ≥ 0` (the constant of
`P:frequency-row`, chosen before `T, d, ν, C, s, h`) such that for every `T > 0` (in
`p`, with `p.a = a`), every measure `ν` on `ℝ^d` with `ν(B(y,r)) ≤ C r^α` (open balls,
`C ≥ 0`), every `I = [s, s+h] ⊆ [0,T]` with `0 < h ≤ 1`: the input direction holds with
`M = 4 A_T K C h^{2-a} B_α(h)`, and, if `ν` is even, so does the output direction.
This is the TeX proof with `ν_R` replaced by any such `ν`; evenness is used only for the
output direction (line 447). -/
theorem wave_two_variances {α a γ : ℝ} (ha : a < 1) (hαa : α + a < 2) (hγ0 : 0 ≤ γ)
    (hγ : 2 * γ ≤ 1) (hαγ : α + 2 * γ < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : TimeParams, p.a = a → ∀ (d : ℕ) (ν : Measure (Rd d)) (C : ℝ),
      0 ≤ C → (∀ y : Rd d, ∀ r : ℝ, 0 < r → ν (Metric.ball y r) ≤ ENNReal.ofReal (C * r ^ α)) →
      ∀ s h : ℝ, 0 < h → h ≤ 1 → 0 ≤ s → s + h ≤ p.T →
        InputBound p s h ν γ (4 * AT p * K * C * h ^ (2 - a) * FrequencyRow.scaleProfile α h) ∧
        (HomogHypothesis.IsEven ν →
          OutputBound p s h ν γ (4 * AT p * K * C * h ^ (2 - a) * FrequencyRow.scaleProfile α h)) := by
  obtain ⟨K, hK0, hK⟩ := FrequencyRow.frequency_row ha hαa hγ hαγ
  refine ⟨K, hK0, ?_⟩
  rintro p rfl d ν C hC hg s h hh0 hh1 hs hsT
  have := isLocallyFinite_of_growth hg
  set B := FrequencyRow.scaleProfile α h with hB
  have hB1 : 1 ≤ B := FrequencyRow.one_le_scaleProfile α hh0 hh1
  set c : ℝ := 4 * AT p * h ^ (2 - p.a) with hc
  have hc0 : 0 ≤ c := by
    have := AT_nonneg p; have := Real.rpow_nonneg hh0.le (2 - p.a); positivity
  set R : Rd d → ℝ := fun ξ => K * C * B * bracket ‖ξ‖ ^ (-(2 * γ)) with hR
  have hR0 : ∀ ξ, 0 ≤ R ξ := fun ξ => by
    have := Real.rpow_nonneg (FrequencyRow.bracket_pos ‖ξ‖).le (-(2 * γ)); positivity
  -- the row bound `E:variance-actual-row-bound`
  have hrow : ∀ ξ : Rd d, ∫⁻ l, ENNReal.ofReal (rowKernel p.a h ξ (ξ - l)) ∂ν ≤
      ENNReal.ofReal (R ξ) := by
    intro ξ
    obtain ⟨hint, hle⟩ := (hK d ν C hC hg h hh0 hh1).2 ξ
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun l => FrequencyRow.rowKernel_nonneg _ _ _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hbp : 0 < bracket ‖ξ‖ ^ (2 * γ) := Real.rpow_pos_of_pos (FrequencyRow.bracket_pos _) _
    simp only [hR]
    rw [Real.rpow_neg (FrequencyRow.bracket_pos _).le, ← div_eq_mul_inv, le_div_iff₀ hbp]
    linarith
  have hm1 : Continuous fun z : Rd d × Rd d => (z.2, z.2 - z.1) := by fun_prop
  have hm2 : Continuous fun z : Rd d × Rd d => (z.2 + z.1, z.2) := by fun_prop
  have hcontΨ : Continuous fun z : Rd d × Rd d => rowKernel p.a h z.2 (z.2 - z.1) :=
    Continuous.congr ((continuous_rowKernel₂ (d := d) p.a h).comp hm1) fun _ => rfl
  have hcontΨ' : Continuous fun z : Rd d × Rd d => rowKernel p.a h (z.2 + z.1) z.2 :=
    Continuous.congr ((continuous_rowKernel₂ (d := d) p.a h).comp hm2) fun _ => rfl
  have hfinal : ∀ S : Rd d → ℝ, Integrable (fun ξ => bracket ‖ξ‖ ^ (-(2 * γ)) * S ξ) →
      ENNReal.ofReal (c * ∫ ξ, R ξ * S ξ) = ENNReal.ofReal (4 * AT p * K * C * h ^ (2 - p.a) *
        B * ∫ ξ, bracket ‖ξ‖ ^ (-(2 * γ)) * S ξ) := by
    intro S _
    congr 1
    simp only [hR, hc, mul_assoc]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
    ring
  have hSm : ∀ W : Fin 2 → Rd d → ℂ, (∀ i, MemLp (W i) 2 volume) →
      AEMeasurable (fun ξ => ∑ i, ‖W i ξ‖ ^ 2) volume := fun W hW =>
    Finset.aemeasurable_fun_sum _ fun i _ => ((hW i).aestronglyMeasurable.norm.pow 2).aemeasurable
  have hRS : ∀ W : Fin 2 → Rd d → ℂ, (∀ i, MemLp (W i) 2 volume) →
      Integrable (fun ξ => R ξ * ∑ i, ‖W i ξ‖ ^ 2) := fun W hW => by
    have := (integrable_weight hγ0 W hW).const_mul (K * C * B)
    simpa only [hR, mul_assoc] using this
  refine ⟨fun n U hU V hV => ⟨fun l k => (input_fixed p hh0 hh1 hs hsT U hU V hV l).1 k,
    integrable_weight hγ0 V hV, ?_⟩, fun hev U hU n V hV =>
      ⟨fun l k => (output_fixed p hh0 hh1 hs hsT U hU V hV l).1 k,
        integrable_weight hγ0 U hU, ?_⟩⟩
  · rw [← hfinal _ (integrable_weight hγ0 V hV)]
    exact total_of_fixed p (fun k l => coef p s h (U k) V l) (fun ξ => ∑ i, ‖V i ξ‖ ^ 2)
      (hSm V hV) (fun l ξ => rowKernel p.a h ξ (ξ - l)) hcontΨ c hc0 R
      (fun l => (input_fixed p hh0 hh1 hs hsT U hU V hV l).2) hrow
      (fun ξ => Finset.sum_nonneg fun i _ => sq_nonneg _) (hRS V hV) hR0
  · rw [← hfinal _ (integrable_weight hγ0 U hU)]
    have hrow' : ∀ η : Rd d, ∫⁻ l, ENNReal.ofReal (rowKernel p.a h (η + l) η) ∂ν ≤
        ENNReal.ofReal (R η) := by
      intro η
      have hm : Measurable fun l : Rd d => ENNReal.ofReal (rowKernel p.a h (η + l) η) :=
        ENNReal.measurable_ofReal.comp (Continuous.congr ((continuous_rowKernel₂ (d := d) p.a h).comp
          (by fun_prop : Continuous fun l : Rd d => (η + l, η))) fun _ => rfl).measurable
      calc ∫⁻ l, ENNReal.ofReal (rowKernel p.a h (η + l) η) ∂ν
          = ∫⁻ l, ENNReal.ofReal (rowKernel p.a h (η + l) η) ∂(ν.map fun x => -x) := by
            rw [hev]
        _ = ∫⁻ l, ENNReal.ofReal (rowKernel p.a h η (η - l)) ∂ν := by
            rw [lintegral_map hm measurable_neg]
            congr 1; funext l
            rw [← sub_eq_add_neg, rowKernel_symm]
        _ ≤ _ := hrow η
    exact total_of_fixed p (fun k l => coef p s h U (V k) l) (fun η => ∑ j, ‖U j η‖ ^ 2)
      (hSm U hU) (fun l η => rowKernel p.a h (η + l) η) hcontΨ' c hc0 R
      (fun l => (output_fixed p hh0 hh1 hs hsT U hU V hV l).2) hrow'
      (fun ξ => Finset.sum_nonneg fun i _ => sq_nonneg _) (hRS U hU) hR0


/-- Auxiliary (Lean proof route): `InputBound` is monotone in the constant. -/
theorem InputBound.mono {p : TimeParams} {d : ℕ} {s h : ℝ} {ν : Measure (Rd d)} {γ M M' : ℝ}
    (hM : M ≤ M') (hb : InputBound p s h ν γ M) : InputBound p s h ν γ M' := by
  intro n U hU V hV
  obtain ⟨h1, h2, h3⟩ := hb n U hU V hV
  refine ⟨h1, h2, h3.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have : 0 ≤ ∫ ξ, bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ i, ‖V i ξ‖ ^ 2 := integral_nonneg fun ξ =>
    mul_nonneg (Real.rpow_nonneg (FrequencyRow.bracket_pos _).le _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_right hM this

/-- Auxiliary (Lean proof route): `OutputBound` is monotone in the constant. -/
theorem OutputBound.mono {p : TimeParams} {d : ℕ} {s h : ℝ} {ν : Measure (Rd d)} {γ M M' : ℝ}
    (hM : M ≤ M') (hb : OutputBound p s h ν γ M) : OutputBound p s h ν γ M' := by
  intro U hU n V hV
  obtain ⟨h1, h2, h3⟩ := hb U hU n V hV
  refine ⟨h1, h2, h3.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have : 0 ≤ ∫ ξ, bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ j, ‖U j ξ‖ ^ 2 := integral_nonneg fun ξ =>
    mul_nonneg (Real.rpow_nonneg (FrequencyRow.bracket_pos _).le _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_right hM this

/-- The `h^{2β}` form of the spectral core (TeX lines 381-382, 453-455): if moreover
`2β < 2 - a` and `2β < 3 - a - α`, there is `K_β ≥ 0` (chosen before `T, d, ν, C, s, h`)
with both directions holding for `M = 4 A_T K_β C h^{2β}`. Proof: the time-scale step
`FrequencyRow.scale_time_le` of `C:frequency-time` (`h^{2-a} B_α(h) ≤ c h^{2β}`) applied to
`wave_two_variances`; the TeX applies the corollary itself to `h^{2-a}` times the row
integral, which is the same inequality. -/
theorem wave_two_variances_beta {α a γ β : ℝ} (ha : a < 1) (hαa : α + a < 2) (hγ0 : 0 ≤ γ)
    (hγ : 2 * γ ≤ 1) (hαγ : α + 2 * γ < 2) (hβa : 2 * β < 2 - a) (hβα : 2 * β < 3 - a - α) :
    ∃ Kβ : ℝ, 0 ≤ Kβ ∧ ∀ p : TimeParams, p.a = a → ∀ (d : ℕ) (ν : Measure (Rd d)) (C : ℝ),
      0 ≤ C → (∀ y : Rd d, ∀ r : ℝ, 0 < r → ν (Metric.ball y r) ≤ ENNReal.ofReal (C * r ^ α)) →
      ∀ s h : ℝ, 0 < h → h ≤ 1 → 0 ≤ s → s + h ≤ p.T →
        InputBound p s h ν γ (4 * AT p * Kβ * C * h ^ (2 * β)) ∧
        (HomogHypothesis.IsEven ν → OutputBound p s h ν γ (4 * AT p * Kβ * C * h ^ (2 * β))) := by
  obtain ⟨K, hK0, hK⟩ := wave_two_variances ha hαa hγ0 hγ hαγ
  obtain ⟨c, hc0, hc⟩ := FrequencyRow.scale_time_le (α := α) hβa hβα
  refine ⟨K * c, mul_nonneg hK0 hc0, ?_⟩
  intro p hpa d ν C hC hg s h hh0 hh1 hs hsT
  obtain ⟨hin, hout⟩ := hK p hpa d ν C hC hg s h hh0 hh1 hs hsT
  have hM : 4 * AT p * K * C * h ^ (2 - a) * FrequencyRow.scaleProfile α h ≤
      4 * AT p * (K * c) * C * h ^ (2 * β) := by
    have h1 := hc h hh0 hh1
    have h2 : 0 ≤ 4 * AT p * K * C := by have := AT_nonneg p; positivity
    calc 4 * AT p * K * C * h ^ (2 - a) * FrequencyRow.scaleProfile α h
        = (4 * AT p * K * C) * (h ^ (2 - a) * FrequencyRow.scaleProfile α h) := by ring
      _ ≤ (4 * AT p * K * C) * (c * h ^ (2 * β)) := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  exact ⟨hin.mono hM, fun hev => (hout hev).mono hM⟩

/-- `C_ν = c_d² L_ζ² C_Γ` of `E:variance-actual-growth-constant` (TeX lines 205-208), with
`L_ζ = MaskedAuxiliaryNorm.Lz ζ = ‖ζ̂‖₁` and `C_Γ = MaskedSpectralGrowth.CGamma Γ`. -/
def Cnu {d : ℕ} (Γ : Measure (Rd d)) (ζ : SchwartzMap (Rd d) ℝ) : ℝ :=
  MaskedAuxiliaryNorm.cd d ^ 2 * MaskedAuxiliaryNorm.Lz ζ ^ 2 * MaskedSpectralGrowth.CGamma Γ

/-- Auxiliary (Lean proof route): `C_ν ≥ 0`. -/
theorem Cnu_nonneg {d : ℕ} (Γ : Measure (Rd d)) (ζ : SchwartzMap (Rd d) ℝ) : 0 ≤ Cnu Γ ζ := by
  unfold Cnu MaskedSpectralGrowth.CGamma MaskedSpectralGrowth.MGamma
  have : 0 ≤ ∫ x, Real.exp (-(‖x‖ ^ 2 / 4)) ∂Γ := integral_nonneg fun x => (Real.exp_pos _).le
  positivity

/-- Under `H:homog`, `ν_R(B(y,r)) ≤ C_ν r^α` for every real Schwartz `ζ`, `R > 0`, `y`,
`r > 0` (TeX lines 209-210, from `P:masked-auxiliary-norm`; no `Γ ≠ 0` and no
`ζ ≠ 0` needed). -/
theorem nu_growth {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (ζ : SchwartzMap (Rd d) ℝ)
    {R : ℝ} (hR : 0 < R) (y : Rd d) (r : ℝ) (hr : 0 < r) :
    MaskedAuxiliaryNorm.nu μ ζ R (Metric.ball y r) ≤ ENNReal.ofReal (Cnu Γ ζ * r ^ alpha) := by
  have := hH.μ_radon
  exact MaskedAuxiliaryNorm.nu_ball_le hH.μ_tempered hH.spectral hH.scaling hR y hr

/-- **The spectral core of `P:wave-two-variances` for the manuscript's `ν_R`**, with the
section's hypotheses: `H:homog` with `a = α₀` (`p.a = alpha0`), `T > 0` (in `p`),
`0 < γ < min(1/2, (2-α)/2)` (`E:variance-gamma-range`), and the mask `ζ` of TeX lines
186-187 (real, even, nonnegative Schwartz, `ζ = 1` on `B_1`, `ζ = 0` off `B_2`; smooth
with compact support). There is `K ≥ 0` (depending only on `α, α₀, γ`) such that for
every `R > 0` and `I = [t₀, t₀+h] ⊆ [0,T]`, `0 < h ≤ 1`, both directions hold for
`ν = ν_R` (`MaskedAuxiliaryNorm.nu μ ζ R`) with `M = C_T h^{2-a} B_α(h)`,
`C_T = 4 A_T K C_ν` (TeX line 432). `Γ = 0` is allowed (then `ν_R = 0`).
The hypotheses `_hζe`, `_hζ0`, `_hζ1`, `_hζ2` are carried for fidelity and unused (the
growth and evenness of `ν_R` hold for every real Schwartz `ζ`). -/
theorem wave_two_variances_core_paper {d : ℕ} {alpha alpha0 γ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (_hγ0 : 0 < γ)
    (hγ : γ < min (1 / 2) ((2 - alpha) / 2)) (p : TimeParams) (hpa : p.a = alpha0)
    (ζ : SchwartzMap (Rd d) ℝ) (_hζe : ∀ x, ζ (-x) = ζ x) (_hζ0 : ∀ x, 0 ≤ ζ x)
    (_hζ1 : ∀ x : Rd d, ‖x‖ ≤ 1 → ζ x = 1) (_hζ2 : ∀ x : Rd d, 2 ≤ ‖x‖ → ζ x = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ t0 h : ℝ, 0 < h → h ≤ 1 → 0 ≤ t0 → t0 + h ≤ p.T →
      InputBound p t0 h (MaskedAuxiliaryNorm.nu μ ζ R) γ
        (4 * AT p * K * Cnu Γ ζ * h ^ (2 - alpha0) * FrequencyRow.scaleProfile alpha h) ∧
      OutputBound p t0 h (MaskedAuxiliaryNorm.nu μ ζ R) γ
        (4 * AT p * K * Cnu Γ ζ * h ^ (2 - alpha0) * FrequencyRow.scaleProfile alpha h) := by
  rw [lt_min_iff] at hγ
  obtain ⟨K, hK0, hK⟩ := wave_two_variances (α := alpha) (a := alpha0) (γ := γ)
    hH.alpha0_lt_one (by linarith [hH.threshold]) _hγ0.le (by linarith) (by linarith)
  refine ⟨K, hK0, fun R hR t0 h hh0 hh1 ht0 hT => ?_⟩
  obtain ⟨hin, hout⟩ := hK p hpa d _ (Cnu Γ ζ) (Cnu_nonneg Γ ζ) (nu_growth hH ζ hR) t0 h hh0 hh1
    ht0 hT
  exact ⟨hin, hout (MaskedAuxiliaryNorm.isEven_nu hR.ne' hH.μ_even)⟩

/-- The `h^{2β}` form of `wave_two_variances_core_paper`: for `β` in `E:variance-beta-range`
(`1/2 < β < min(1 - a/2, (3-a-α)/2)`) there is `K_β ≥ 0` with both directions for `ν_R`
and `M = 4 A_T K_β C_ν h^{2β}`. `1/2 < β` and the mask hypotheses are carried, unused. -/
theorem wave_two_variances_core_beta_paper {d : ℕ} {alpha alpha0 γ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (_hγ0 : 0 < γ)
    (hγ : γ < min (1 / 2) ((2 - alpha) / 2)) (p : TimeParams) (hpa : p.a = alpha0)
    (ζ : SchwartzMap (Rd d) ℝ) (_hζe : ∀ x, ζ (-x) = ζ x) (_hζ0 : ∀ x, 0 ≤ ζ x)
    (_hζ1 : ∀ x : Rd d, ‖x‖ ≤ 1 → ζ x = 1) (_hζ2 : ∀ x : Rd d, 2 ≤ ‖x‖ → ζ x = 0)
    (β : ℝ) (_hβ0 : 1 / 2 < β) (hβ : β < min (1 - alpha0 / 2) ((3 - alpha0 - alpha) / 2)) :
    ∃ Kβ : ℝ, 0 ≤ Kβ ∧ ∀ R : ℝ, 0 < R → ∀ t0 h : ℝ, 0 < h → h ≤ 1 → 0 ≤ t0 → t0 + h ≤ p.T →
      InputBound p t0 h (MaskedAuxiliaryNorm.nu μ ζ R) γ
        (4 * AT p * Kβ * Cnu Γ ζ * h ^ (2 * β)) ∧
      OutputBound p t0 h (MaskedAuxiliaryNorm.nu μ ζ R) γ
        (4 * AT p * Kβ * Cnu Γ ζ * h ^ (2 * β)) := by
  rw [lt_min_iff] at hγ hβ
  obtain ⟨K, hK0, hK⟩ := wave_two_variances_beta (α := alpha) (a := alpha0) (γ := γ) (β := β)
    hH.alpha0_lt_one (by linarith [hH.threshold]) _hγ0.le (by linarith) (by linarith)
    (by linarith) (by linarith)
  refine ⟨K, hK0, fun R hR t0 h hh0 hh1 ht0 hT => ?_⟩
  obtain ⟨hin, hout⟩ := hK p hpa d _ (Cnu Γ ζ) (Cnu_nonneg Γ ζ) (nu_growth hH ζ hR) t0 h hh0 hh1
    ht0 hT
  exact ⟨hin, hout (MaskedAuxiliaryNorm.isEven_nu hR.ne' hH.μ_even)⟩

/-- Auxiliary (Lean proof route): `∑ ofReal x_k ≤ ofReal A`, `A ≥ 0` gives `∑ x_k ≤ A`. -/
theorem sum_le_of_ofReal {n : ℕ} (x : Fin n → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (h : ∑ k, ENNReal.ofReal (x k) ≤ ENNReal.ofReal A) : ∑ k, x k ≤ A := by
  calc ∑ k, x k ≤ ∑ k, (ENNReal.ofReal (x k)).toReal :=
        Finset.sum_le_sum fun k _ => by rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
    _ = (∑ k, ENNReal.ofReal (x k)).toReal :=
        (ENNReal.toReal_sum fun k _ => ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal A).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = A := ENNReal.toReal_ofReal hA

/-- Auxiliary (Lean proof route): an inner-product-preserving `J` maps an orthonormal family
of `P` to an `L²(ℝ^d; ℂ²)`-orthonormal family (TeX line 413: `U_k = J e_k`). -/
theorem orthonormal_J {d : ℕ} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    (J : P → Fin 2 → Rd d → ℂ) (hJL2 : ∀ z i, MemLp (J z i) 2 volume)
    (hJ : ∀ z w, ∫ η, ∑ j, J z j η * conj (J w j η) = inner ℂ w z)
    {n : ℕ} {e : Fin n → P} (he : Orthonormal ℂ e) :
    PhaseBessel.IsOrthonormalL2 volume fun k => J (e k) := by
  refine ⟨fun k i => hJL2 _ _, fun k l => ?_⟩
  rw [hJ, orthonormal_iff_ite.1 he l k]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl, Ne.symm hkl]

/-- **`P:wave-two-variances`** (TeX lines 368-383) with the manuscript's hypotheses and two
named inputs; NARROWER than the TeX (see the module doc). Hypotheses: those of
`wave_two_variances_core_paper`; `P` a complex inner product space standing for the
Schwartz phases with the complexified `E` inner product; and:
* `J`, `hJL2`, `hJ` (D8, TeX lines 171-176): `J : P → L²(ℝ^d; ℂ²)` preserves inner
  products, `∫ ∑_j (Jz)_j conj (Jw)_j = ⟨z, w⟩_E` (Mathlib's `inner ℂ w z`, which is linear
  in `z`);
* `normSG`, `hnormSG` (D8, TeX line 431): `‖z‖²_{E_{s-γ}} = ∫ ⟨ξ⟩^{-2γ} ∑|(Jz)_i|²`;
* `var`, `hlink` (`E:variance-normalized-covariance`, TeX lines 240-246, from
  `P:actual-wave-form`, which needs D1): `var R t₀ h z w` stands for
  `E|ℓ_R([t₀,t₀+h]; z, w)|²` and is bounded by the lower integral
  `∫ ‖coef (Jz) (Jw) λ‖² ν_R(dλ)`.
Conclusion: there is `C_T ≥ 0`, independent of `R`, `I` and the family, with
`∑_k var(e_k, z) ≤ C_T h^{2-a} B_α(h) ‖z‖²_{E_{s-γ}}` (`E:wave-input-variance`) and
`∑_k var(z, e_k) ≤ C_T h^{2-a} B_α(h) ‖z‖²_{E_{s-γ}}` (`E:wave-output-variance`) for every
finite orthonormal family `e_k` of `P` and every `z`; and for each `β` in
`E:variance-beta-range` the same with `C_{T,β} h^{2β}`. -/
theorem wave_two_variances_paper {d : ℕ} {alpha alpha0 γ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (hγ0 : 0 < γ)
    (hγ : γ < min (1 / 2) ((2 - alpha) / 2)) (p : TimeParams) (hpa : p.a = alpha0)
    (ζ : SchwartzMap (Rd d) ℝ) (hζe : ∀ x, ζ (-x) = ζ x) (hζ0 : ∀ x, 0 ≤ ζ x)
    (hζ1 : ∀ x : Rd d, ‖x‖ ≤ 1 → ζ x = 1) (hζ2 : ∀ x : Rd d, 2 ≤ ‖x‖ → ζ x = 0)
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    (J : P → Fin 2 → Rd d → ℂ) (hJL2 : ∀ z i, MemLp (J z i) 2 volume)
    (hJ : ∀ z w, ∫ η, ∑ j, J z j η * conj (J w j η) = inner ℂ w z)
    (normSG : P → ℝ)
    (hnormSG : ∀ z, normSG z ^ 2 = ∫ ξ, bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ i, ‖J z i ξ‖ ^ 2)
    (var : ℝ → ℝ → ℝ → P → P → ℝ)
    (hlink : ∀ R : ℝ, 0 < R → ∀ t0 h : ℝ, 0 < h → h ≤ 1 → 0 ≤ t0 → t0 + h ≤ p.T → ∀ z w : P,
      ENNReal.ofReal (var R t0 h z w) ≤
        ∫⁻ l, ‖coef p t0 h (J z) (J w) l‖ₑ ^ 2 ∂(MaskedAuxiliaryNorm.nu μ ζ R)) :
    (∃ CT : ℝ, 0 ≤ CT ∧ ∀ R : ℝ, 0 < R → ∀ t0 h : ℝ, 0 < h → h ≤ 1 → 0 ≤ t0 →
      t0 + h ≤ p.T → ∀ (n : ℕ) (e : Fin n → P), Orthonormal ℂ e → ∀ z : P,
        ∑ k, var R t0 h (e k) z ≤
          CT * h ^ (2 - alpha0) * FrequencyRow.scaleProfile alpha h * normSG z ^ 2 ∧
        ∑ k, var R t0 h z (e k) ≤
          CT * h ^ (2 - alpha0) * FrequencyRow.scaleProfile alpha h * normSG z ^ 2) ∧
    ∀ β : ℝ, 1 / 2 < β → β < min (1 - alpha0 / 2) ((3 - alpha0 - alpha) / 2) →
      ∃ CTβ : ℝ, 0 ≤ CTβ ∧ ∀ R : ℝ, 0 < R → ∀ t0 h : ℝ, 0 < h → h ≤ 1 → 0 ≤ t0 →
        t0 + h ≤ p.T → ∀ (n : ℕ) (e : Fin n → P), Orthonormal ℂ e → ∀ z : P,
          ∑ k, var R t0 h (e k) z ≤ CTβ * h ^ (2 * β) * normSG z ^ 2 ∧
          ∑ k, var R t0 h z (e k) ≤ CTβ * h ^ (2 * β) * normSG z ^ 2 := by
  have hw : ∀ z, 0 ≤ ∫ ξ, bracket ‖ξ‖ ^ (-(2 * γ)) * ∑ i, ‖J z i ξ‖ ^ 2 := fun z =>
    integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (FrequencyRow.bracket_pos _).le _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  -- generic transfer from the spectral core to the abstract variances
  have transfer : ∀ (M : ℝ) (R : ℝ), 0 < R → ∀ t0 h : ℝ, 0 < h → h ≤ 1 → 0 ≤ t0 →
      t0 + h ≤ p.T → 0 ≤ M →
      InputBound p t0 h (MaskedAuxiliaryNorm.nu μ ζ R) γ M →
      OutputBound p t0 h (MaskedAuxiliaryNorm.nu μ ζ R) γ M →
      ∀ (n : ℕ) (e : Fin n → P), Orthonormal ℂ e → ∀ z : P,
        ∑ k, var R t0 h (e k) z ≤ M * normSG z ^ 2 ∧
        ∑ k, var R t0 h z (e k) ≤ M * normSG z ^ 2 := by
    intro M R hR t0 h hh0 hh1 ht0 hT hM hin hout n e he z
    have hU := orthonormal_J J hJL2 hJ he
    rw [hnormSG]
    refine ⟨sum_le_of_ofReal _ (mul_nonneg hM (hw z)) ?_,
      sum_le_of_ofReal _ (mul_nonneg hM (hw z)) ?_⟩
    · exact (Finset.sum_le_sum fun k _ => hlink R hR t0 h hh0 hh1 ht0 hT (e k) z).trans
        (hin n (fun k => J (e k)) hU (J z) (hJL2 z)).2.2
    · exact (Finset.sum_le_sum fun k _ => hlink R hR t0 h hh0 hh1 ht0 hT z (e k)).trans
        (hout (J z) (hJL2 z) n (fun k => J (e k)) hU).2.2
  refine ⟨?_, fun β hβ0 hβ => ?_⟩
  · obtain ⟨K, hK0, hK⟩ := wave_two_variances_core_paper hH hγ0 hγ p hpa ζ hζe hζ0 hζ1 hζ2
    refine ⟨4 * AT p * K * Cnu Γ ζ, by have := AT_nonneg p; have := Cnu_nonneg Γ ζ; positivity,
      fun R hR t0 h hh0 hh1 ht0 hT n e he z => ?_⟩
    have hB := FrequencyRow.one_le_scaleProfile alpha hh0 hh1
    have hM : 0 ≤ 4 * AT p * K * Cnu Γ ζ * h ^ (2 - alpha0) * FrequencyRow.scaleProfile alpha h := by
      have := AT_nonneg p; have := Cnu_nonneg Γ ζ; have := Real.rpow_nonneg hh0.le (2 - alpha0)
      positivity
    obtain ⟨hin, hout⟩ := hK R hR t0 h hh0 hh1 ht0 hT
    have := transfer _ R hR t0 h hh0 hh1 ht0 hT hM hin hout n e he z
    rw [hnormSG] at this ⊢
    exact this
  · obtain ⟨K, hK0, hK⟩ := wave_two_variances_core_beta_paper hH hγ0 hγ p hpa ζ hζe hζ0 hζ1 hζ2
      β hβ0 hβ
    refine ⟨4 * AT p * K * Cnu Γ ζ, by have := AT_nonneg p; have := Cnu_nonneg Γ ζ; positivity,
      fun R hR t0 h hh0 hh1 ht0 hT n e he z => ?_⟩
    have hM : 0 ≤ 4 * AT p * K * Cnu Γ ζ * h ^ (2 * β) := by
      have := AT_nonneg p; have := Cnu_nonneg Γ ζ; have := Real.rpow_nonneg hh0.le (2 * β)
      positivity
    obtain ⟨hin, hout⟩ := hK R hR t0 h hh0 hh1 ht0 hT
    have := transfer _ R hR t0 h hh0 hh1 ht0 hT hM hin hout n e he z
    rw [hnormSG] at this ⊢
    exact this


end StratonovichHAMSecondMoment.WaveTwoVariances
