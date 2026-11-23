module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L11 item K2: the named input `FockForm.FockColumn` (the spatial column bound) of
`FockForm.fock_form_paper` (`L:fock-form`) and `FockForm.interval_contractions_paper`
(`L:interval-contractions`, display `E:interval-column`) is proved on a concrete `L²` model,
in `notes/notes_stratonovich_ham_second_moment.tex` (main TeX; line numbers at revision
edf7085f).  The abstract wrappers of `FockForm` are unchanged; the `_completed` theorems here
are those wrappers instantiated at the concrete operators, with every operator input proved.

The concrete model (Fourier side).  Spatial `L²(ℝ^d)` enters through its Fourier image: the
Hilbert space is `X = L²(ℝ^d, dη)` (`Lp ℂ 2 volume`), read as `f̂/(2π)^{d/2}`, so that the
normalized Fourier transform is unitary and Plancherel is built in.  On this side:
* `A_ρ^{-1/2}` (`A_ρ = ρ² - Δ`) is multiplication by `w_ρ(η) = (ρ² + |η|²)^{-1/2}`
  (`sqrtResolvent ρ`, `wt`); it is self-adjoint with `‖A_ρ^{-1/2}‖ ≤ ρ^{-1}`;
* the band projection `S_b` onto `|η| ≤ b` is multiplication by `1_{|η| ≤ b}` (`bandProj b`);
  it is self-adjoint, idempotent and commutes with `A_ρ^{-1/2}`;
* the smoothed field `W_ε` has spectral measure `μ_ε(dξ) = e^{-ε|ξ|²} μ(dξ)` (`nuEps μ ε`;
  `Γ_ε = p_{2ε} * Γ`, lines 2505-2506 and 3394; the weight is the one in `J_{ρ,ε}`, lines
  2998-3000); it is finite (`μ` tempered, `ε > 0`) and even (`μ` even);
* the Gaussian modes are an orthonormal family `ψ_1, …, ψ_m` in `L²(μ_ε)`; the mode is
  `e_i(x) = ∫ e^{ix·ξ} conj(ψ_i(ξ)) μ_ε(dξ)`, real-valued exactly when
  `ψ_i(-ξ) = conj ψ_i(ξ)` `μ_ε`-a.e. (hypothesis `hreal`).  For such `ψ_i` the complex
  `L²(μ_ε)` inner products are real, so orthonormality in the real isonormal space (TeX,
  lines 2987-2988) is orthonormality here.  Multiplication by `e_i` is, on the Fourier side,
  `(M_{e_i} f)(η) = ∫ conj(ψ_i(ξ)) f(η - ξ) μ_ε(dξ)` (`conv`, `modeOp`, `modes`); it is
  bounded by `√(μ_ε(ℝ^d)) = √(Γ_ε(0))` (the TeX's `|e_i| ≤ √v_ε`, line 2989) and
  self-adjoint for real modes (`modeOp_isSelfAdjoint`: Fubini, translation invariance,
  evenness).
The correspondence of these Fourier-side operators with the TeX's physical-space operators
(conjugation by the unitary Fourier transform, and `(e f)^ = conj ψ μ_ε * f̂`) is classical and
is not formalized; the completed theorems are statements about the Fourier-side operators.
Every conclusion of the wrappers (norms, self-adjointness, column bounds) is invariant under
that unitary conjugation.

Formalized:
* `column_bound` (`E:interval-column`, lines 3388-3391, proof 3437-3445): for a finite `ν`,
  an orthonormal family in `L²(ν)` and a uniform resolvent bound
  `∫ ν(dξ)/(ρ² + |q+ξ|²) ≤ c`: `∑_i ‖A_ρ^{-1/2} M_{ψ_i} f‖² ≤ c ‖f‖²`.  The TeX's Gaussian
  isometry and Plancherel identity (an equality for the full mode family) is replaced by
  Bessel's inequality in `L²(ν)` at each frequency `η` (`sum_conv_le`, "a finite mode sum is
  a positive sub-sum", line 3444), followed by Tonelli and translation invariance
  (`lintegral_weight_shift`).
* `nuEps_resolvent` (`E:phase-resolvent` for `μ_ε`, lines 2512-2514 and 3427-3430):
  from `PhaseContractions.phase_resolvent` (proved, no supplied input) and `e^{-ε|ξ|²} ≤ 1`.
* `column_sandwich` (substitution, lines 3455-3459; also lines 3004-3005).
* `interval_column_completed` (under `H:homog`) and `fock_column_completed` (under the class
  of `S:static-phase`, with self-adjointness of `H_i`, lines 2989-2991): the `FockColumn`
  inputs, proved for the concrete operators.
* `fock_form_paper_completed` (`L:fock-form`, statement 2960-2977, proof 2979-3028) and
  `interval_contractions_paper_completed` (`L:interval-contractions`, statement 3384-3404,
  proof 3406-3470): the `FockForm` wrappers at the concrete operators with all inputs
  discharged (`FockColumn`, self-adjointness of `H_i`, `M_i`, `S`, `P`; `‖S‖ ≤ ρ^{-1}`;
  `P² = P`; `PS = SP`).

Supplied inputs: none.  Hypotheses of the completed theorems beyond the manuscript's class:
the concrete choice of modes (`ψ` orthonormal in `L²(μ_ε)`, real modes `hreal`), which is
the TeX's "choose an orthonormal basis of the real isonormal space" restricted to finitely
many modes, and the band radius `b`.  `fock_form_paper_completed` assumes
`PhaseContractions.PhaseCovariance` (the class of `S:static-phase` as recorded there,
including `μ` even and tempered, which `FockForm.fock_form_paper` did not list because it
did not use them).  Carried and unused: `Γ_radon`, `Γ_even`, `Γ_tempered`, `Γ_posdef` (in
both wrappers), and `dim`, `alpha0_lt_one` of `H:homog`.

Narrower than the TeX: finitely many modes (the TeX: all modes, and a finite family is a
sub-sum); the identification with physical-space operators is not formalized (above).
Junk values: `ρ > 0` and `ε > 0` throughout; `1/(ρ² + |η|²)` has a positive denominator. -/
public import Mathlib
public import StratonovichHAMSecondMoment.FockForm
public import StratonovichHAMSecondMoment.PhaseContractions

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate

namespace StratonovichHAMSecondMoment.FockColumnBound

open HomogHypothesis (Rd)

/-! ### Square-integrable functions and bounded maps on `L²` -/

section General

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Auxiliary: `‖f‖_{L²}² = ∫⁻ ‖f‖ₑ²` for an a.e. strongly measurable `f`. -/
theorem eLpNorm_two_sq {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Auxiliary: a strongly measurable `f` with `∫⁻ ‖f‖ₑ² < ∞` is in `L²`. -/
theorem memLp_two_of_lintegral {f : α → ℂ} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ ≠ ⊤) : MemLp f 2 μ := by
  have hlt : eLpNorm f 2 μ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h'
    apply h
    rw [← eLpNorm_two_sq hf, h']
    simp
  exact hlt

/-- Auxiliary: the `L²` norm squared is the lower integral of `‖f‖ₑ²`. -/
theorem norm_sq_Lp (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = (∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ).toReal := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow, eLpNorm_two_sq (Lp.aestronglyMeasurable f)]

/-- Auxiliary: elements of `L²` have finite `∫⁻ ‖f‖ₑ²`. -/
theorem lintegral_Lp_ne_top (f : Lp ℂ 2 μ) : ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  rw [← eLpNorm_two_sq (Lp.aestronglyMeasurable f)]
  exact ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)

/-- Auxiliary: the norm squared of `toLp`. -/
theorem norm_sq_toLp {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = (∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ).toReal := by
  rw [norm_sq_Lp]
  congr 1
  exact lintegral_congr_ae (hf.coeFn_toLp.mono fun a ha => by simp only [ha])

/-- The data of a bounded linear map on `L²(μ)` given on representatives: a map `F` on
functions, measurable on `L²` classes, additive and homogeneous up to null sets, with
`∫⁻ ‖F f‖ₑ² ≤ C ∫⁻ ‖f‖ₑ²`. -/
structure L2Map (μ : Measure α) where
  /-- The map on representatives. -/
  F : (α → ℂ) → α → ℂ
  /-- The bound `C` (finite). -/
  C : ℝ≥0∞
  C_ne_top : C ≠ ⊤
  meas : ∀ f : Lp ℂ 2 μ, AEStronglyMeasurable (F f) μ
  bound : ∀ f : Lp ℂ 2 μ, ∫⁻ a, ‖F f a‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ
  add : ∀ f g : Lp ℂ 2 μ, F ⇑(f + g) =ᵐ[μ] F f + F g
  smul : ∀ (c : ℂ) (f : Lp ℂ 2 μ), F ⇑(c • f) =ᵐ[μ] c • F f

namespace L2Map

variable (T : L2Map μ)

/-- Auxiliary: `F f ∈ L²` for every `L²` class `f`. -/
theorem memLp (f : Lp ℂ 2 μ) : MemLp (T.F f) 2 μ :=
  memLp_two_of_lintegral (T.meas f)
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top T.C_ne_top (lintegral_Lp_ne_top f)) (T.bound f))

/-- The linear map on `L²` classes. -/
def toLinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (T.memLp f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 (T.add f g)
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 (T.smul c f)

/-- Auxiliary: `‖T f‖² ≤ C ‖f‖²`. -/
theorem norm_sq_le (f : Lp ℂ 2 μ) : ‖T.toLinear f‖ ^ 2 ≤ T.C.toReal * ‖f‖ ^ 2 := by
  change ‖(T.memLp f).toLp _‖ ^ 2 ≤ _
  rw [norm_sq_toLp, norm_sq_Lp, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top T.C_ne_top (lintegral_Lp_ne_top f)) (T.bound f)

/-- Auxiliary: `‖T f‖ ≤ √C ‖f‖`. -/
theorem norm_le (f : Lp ℂ 2 μ) : ‖T.toLinear f‖ ≤ √T.C.toReal * ‖f‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  exact T.norm_sq_le f

/-- The bounded linear operator on `L²(μ)` defined by `T`. -/
def op : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  T.toLinear.mkContinuous (√T.C.toReal) T.norm_le

/-- The operator acts by `F` on representatives, up to null sets. -/
theorem op_ae (f : Lp ℂ 2 μ) : T.op f =ᵐ[μ] T.F f :=
  (T.memLp f).coeFn_toLp

/-- The norm bound `‖T f‖ ≤ √C ‖f‖` of the operator. -/
theorem op_norm_le (f : Lp ℂ 2 μ) : ‖T.op f‖ ≤ √T.C.toReal * ‖f‖ :=
  T.norm_le f

/-- `‖T f‖² = ∫⁻ ‖F f‖ₑ²` (as a real number). -/
theorem norm_sq_op (f : Lp ℂ 2 μ) : ‖T.op f‖ ^ 2 = (∫⁻ a, ‖T.F f a‖ₑ ^ 2 ∂μ).toReal :=
  norm_sq_toLp (T.memLp f)

end L2Map

/-- Auxiliary: two operators on `L²` that agree a.e. on every class are equal. -/
theorem op_ext {A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (h : ∀ f, (A f : α → ℂ) =ᵐ[μ] B f) : A = B :=
  ContinuousLinearMap.ext fun f => Lp.ext (h f)

/-! ### Multiplication operators -/

/-- Multiplication by a bounded measurable real function `a` (`|a| ≤ B`). -/
def mulMap (a : α → ℝ) (ha : Measurable a) (B : ℝ) (hB : ∀ x, |a x| ≤ B) : L2Map μ where
  F f x := (a x : ℂ) * f x
  C := ENNReal.ofReal (B ^ 2)
  C_ne_top := ENNReal.ofReal_ne_top
  meas f := (Complex.measurable_ofReal.comp ha).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable f)
  bound f := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [enorm_mul, mul_pow]
    gcongr
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  add f g := (Lp.coeFn_add f g).mono fun x hx => by
    simp only [Pi.add_apply]; rw [hx, Pi.add_apply, mul_add]
  smul c f := (Lp.coeFn_smul c f).mono fun x hx => by
    simp only [hx, Pi.smul_apply, smul_eq_mul]; ring

/-- The multiplication operator `M_a` on `L²(μ)`. -/
def mulOp (a : α → ℝ) (ha : Measurable a) (B : ℝ) (hB : ∀ x, |a x| ≤ B) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (mulMap (μ := μ) a ha B hB).op

/-- `M_a f = a f` a.e. -/
theorem mulOp_ae (a : α → ℝ) (ha : Measurable a) (B : ℝ) (hB : ∀ x, |a x| ≤ B)
    (f : Lp ℂ 2 μ) : (mulOp (μ := μ) a ha B hB f : α → ℂ) =ᵐ[μ] fun x => (a x : ℂ) * f x :=
  (mulMap a ha B hB).op_ae f

/-- A real multiplication operator is self-adjoint. -/
theorem mulOp_isSelfAdjoint (a : α → ℝ) (ha : Measurable a) (B : ℝ) (hB : ∀ x, |a x| ≤ B) :
    IsSelfAdjoint (mulOp (μ := μ) a ha B hB) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simp only [ContinuousLinearMap.coe_coe]
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulOp_ae (μ := μ) a ha B hB f, mulOp_ae (μ := μ) a ha B hB g] with x hf hg
  rw [hf, hg, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-- Multiplication operators compose by multiplying the functions. -/
theorem mulOp_comp (a b c : α → ℝ) (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (A B C : ℝ) (hA : ∀ x, |a x| ≤ A) (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C)
    (habc : ∀ x, a x * b x = c x) :
    mulOp (μ := μ) a ha A hA ∘L mulOp b hb B hB = mulOp c hc C hC := by
  refine op_ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply]
  filter_upwards [mulOp_ae (μ := μ) a ha A hA (mulOp b hb B hB f), mulOp_ae (μ := μ) b hb B hB f,
    mulOp_ae (μ := μ) c hc C hC f] with x h1 h2 h3
  rw [h1, h2, h3, ← habc x]
  push_cast
  ring

/-- The norm bound of a multiplication operator: `‖M_a f‖ ≤ B ‖f‖` for `0 ≤ B`. -/
theorem mulOp_norm_le (a : α → ℝ) (ha : Measurable a) (B : ℝ) (hB : ∀ x, |a x| ≤ B)
    (hB0 : 0 ≤ B) (f : Lp ℂ 2 μ) : ‖mulOp (μ := μ) a ha B hB f‖ ≤ B * ‖f‖ := by
  have := (mulMap (μ := μ) a ha B hB).op_norm_le f
  simp only [mulMap, ENNReal.toReal_ofReal (sq_nonneg B), Real.sqrt_sq hB0] at this
  exact this

end General

/-! ### Translates of `L²` functions against a finite spectral measure -/

section Shift

variable {d : ℕ} {ν : Measure (Rd d)}

/-- Auxiliary: `(η, ξ) ↦ η - ξ` maps `Leb ⊗ ν`-null sets back from Lebesgue-null sets. -/
theorem qmp_sub [SFinite ν] :
    QuasiMeasurePreserving (fun p : Rd d × Rd d => p.1 - p.2)
      ((volume : Measure (Rd d)).prod ν) volume := by
  have hm : Measurable (fun p : Rd d × Rd d => p.1 - p.2) := measurable_fst.sub measurable_snd
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hm hs)]
  have h : ∀ ξ : Rd d, (volume : Measure (Rd d))
      ((fun η => (η, ξ)) ⁻¹' ((fun p : Rd d × Rd d => p.1 - p.2) ⁻¹' s)) = 0 := by
    intro ξ
    have he : (fun η => (η, ξ)) ⁻¹' ((fun p : Rd d × Rd d => p.1 - p.2) ⁻¹' s) =
        (fun η => η + -ξ) ⁻¹' s := by
      ext η; simp [sub_eq_add_neg]
    rw [he, measure_preimage_add_right]
    exact h0
  simp [h]

/-- Auxiliary: the translates `ξ ↦ f(η - ξ)` of an `L²` class are strongly measurable. -/
theorem sm_shift (f : Lp ℂ 2 (volume : Measure (Rd d))) (η : Rd d) :
    StronglyMeasurable (fun ξ : Rd d => f (η - ξ)) :=
  (Lp.stronglyMeasurable f).comp_measurable (measurable_const.sub measurable_id)

/-- Auxiliary: `(η, ξ) ↦ f(η - ξ)` is strongly measurable. -/
theorem sm_shift₂ (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    StronglyMeasurable (fun p : Rd d × Rd d => f (p.1 - p.2)) :=
  (Lp.stronglyMeasurable f).comp_measurable (measurable_fst.sub measurable_snd)

/-- Auxiliary (Tonelli and translation invariance of Lebesgue measure): for measurable
`W ≥ 0`, `∫ W(η) ∫ |f(η-ξ)|² ν(dξ) dη = ∫ |f(ζ)|² ∫ W(ζ+ξ) ν(dξ) dζ`. -/
theorem lintegral_weight_shift [SFinite ν] (f : Lp ℂ 2 (volume : Measure (Rd d)))
    (W : Rd d → ℝ≥0∞) (hW : Measurable W) :
    ∫⁻ η, W η * ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν =
      ∫⁻ ζ, ‖f ζ‖ₑ ^ 2 * ∫⁻ ξ, W (ζ + ξ) ∂ν := by
  have hf : Measurable (fun p : Rd d × Rd d => ‖f (p.1 - p.2)‖ₑ ^ 2) :=
    (sm_shift₂ f).measurable.enorm.pow_const 2
  have hfz : Measurable (fun ζ : Rd d => ‖f ζ‖ₑ ^ 2) :=
    (Lp.stronglyMeasurable f).measurable.enorm.pow_const 2
  calc ∫⁻ η, W η * ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν
      = ∫⁻ η, ∫⁻ ξ, W η * ‖f (η - ξ)‖ₑ ^ 2 ∂ν := by
        refine lintegral_congr fun η => ?_
        exact (lintegral_const_mul (W η) ((sm_shift f η).measurable.enorm.pow_const 2)).symm
    _ = ∫⁻ ξ, ∫⁻ η, W η * ‖f (η - ξ)‖ₑ ^ 2 ∂volume ∂ν :=
        lintegral_lintegral_swap (by
          apply Measurable.aemeasurable
          exact (hW.comp measurable_fst).mul hf)
    _ = ∫⁻ ξ, ∫⁻ ζ, W (ζ + ξ) * ‖f ζ‖ₑ ^ 2 ∂volume ∂ν := by
        refine lintegral_congr fun ξ => ?_
        rw [← lintegral_add_right_eq_self _ ξ]
        simp
    _ = ∫⁻ ζ, ∫⁻ ξ, W (ζ + ξ) * ‖f ζ‖ₑ ^ 2 ∂ν ∂volume :=
        lintegral_lintegral_swap (by
          apply Measurable.aemeasurable
          exact (hW.comp (measurable_snd.add measurable_fst)).mul (hfz.comp measurable_snd))
    _ = ∫⁻ ζ, ‖f ζ‖ₑ ^ 2 * ∫⁻ ξ, W (ζ + ξ) ∂ν := by
        refine lintegral_congr fun ζ => ?_
        rw [lintegral_mul_const _ (by fun_prop), mul_comm]

/-- Auxiliary: if `f = g` Lebesgue-a.e., then for a.e. `η`, `f(η-ξ) = g(η-ξ)` for
`ν`-a.e. `ξ` (`ν` s-finite). -/
theorem ae_ae_shift_eq [SFinite ν] {f g : Rd d → ℂ} (h : f =ᵐ[volume] g) :
    ∀ᵐ η ∂(volume : Measure (Rd d)), ∀ᵐ ξ ∂ν, f (η - ξ) = g (η - ξ) :=
  Measure.ae_ae_of_ae_prod (p := fun p : Rd d × Rd d => f (p.1 - p.2) = g (p.1 - p.2))
    ((qmp_sub (ν := ν)).ae_eq_comp h)

/-- Auxiliary: for a finite `ν`, `∫ |f(η-ξ)|² ν(dξ) < ∞` for a.e. `η`. -/
theorem ae_lintegral_shift_lt_top [IsFiniteMeasure ν] (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    ∀ᵐ η ∂(volume : Measure (Rd d)), ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν < ⊤ := by
  have hf : Measurable (fun p : Rd d × Rd d => ‖f (p.1 - p.2)‖ₑ ^ 2) :=
    (sm_shift₂ f).measurable.enorm.pow_const 2
  refine ae_lt_top' (hf.lintegral_prod_right').aemeasurable ?_
  have h := lintegral_weight_shift (ν := ν) f (fun _ => 1) measurable_const
  simp only [one_mul, lintegral_const] at h
  rw [h, lintegral_mul_const _ ((Lp.stronglyMeasurable f).measurable.enorm.pow_const 2)]
  exact ENNReal.mul_ne_top (lintegral_Lp_ne_top f) (measure_ne_top ν univ)

end Shift

/-! ### The Fourier-side multiplication by a Gaussian mode -/

section Conv

variable {d : ℕ}

/-- The Fourier-side form of the multiplication `M_{e}` by the mode
`e(x) = ∫ e^{ix·ξ} conj(ψ(ξ)) ν(dξ)`: `(M_ψ f)(η) = ∫ conj(ψ(ξ)) f(η-ξ) ν(dξ)`. -/
def conv (ν : Measure (Rd d)) (ψ : Rd d → ℂ) (f : Rd d → ℂ) (η : Rd d) : ℂ :=
  ∫ ξ, conj (ψ ξ) * f (η - ξ) ∂ν

variable {ν : Measure (Rd d)}

/-- Auxiliary: on a square-integrable translate, `M_ψ f(η)` is the `L²(ν)` inner product
`⟪ψ, f(η - ·)⟫`. -/
theorem conv_eq_inner (ψ : Lp ℂ 2 ν) {f : Rd d → ℂ} {η : Rd d}
    (hk : MemLp (fun ξ => f (η - ξ)) 2 ν) : conv ν ψ f η = inner ℂ ψ (hk.toLp _) := by
  rw [L2.inner_def, conv]
  refine integral_congr_ae (hk.coeFn_toLp.mono fun ξ hξ => ?_)
  simp only [hξ, RCLike.inner_apply']

/-- Auxiliary: `conj ψ · k` is `ν`-integrable for `ψ, k ∈ L²(ν)`. -/
theorem integrable_conj_mul (ψ : Lp ℂ 2 ν) {k : Rd d → ℂ} (hk : MemLp k 2 ν) :
    Integrable (fun ξ => conj (ψ ξ) * k ξ) ν :=
  (L2.integrable_inner (𝕜 := ℂ) ψ (hk.toLp k)).congr
    (hk.coeFn_toLp.mono fun ξ hξ => by simp only [hξ, RCLike.inner_apply'])

/-- **Bessel's inequality for the modes**: for an orthonormal family `ψ_1, …, ψ_m` in `L²(ν)`
and every `η`, `∑_i |M_{ψ_i} f(η)|² ≤ ∫ |f(η-ξ)|² ν(dξ)`. -/
theorem sum_conv_le {m : ℕ} (ψ : Fin m → Lp ℂ 2 ν) (hψ : Orthonormal ℂ ψ)
    (f : Lp ℂ 2 (volume : Measure (Rd d))) (η : Rd d) :
    ∑ i, ‖conv ν (ψ i) f η‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν := by
  by_cases hI : ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν = ⊤
  · rw [hI]; exact le_top
  have hk := memLp_two_of_lintegral (sm_shift f η).aestronglyMeasurable hI
  have hB := hψ.sum_inner_products_le (s := Finset.univ) (hk.toLp _)
  rw [norm_sq_toLp] at hB
  simp_rw [conv_eq_inner (ψ _) hk]
  calc ∑ i, ‖inner ℂ (ψ i) (hk.toLp _)‖ₑ ^ 2
      = ENNReal.ofReal (∑ i, ‖inner ℂ (ψ i) (hk.toLp _)‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ ENNReal.ofReal ((∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν).toReal) := ENNReal.ofReal_le_ofReal hB
    _ = _ := ENNReal.ofReal_toReal hI

/-- Auxiliary (Cauchy-Schwarz): for a unit `ψ`, `|M_ψ f(η)|² ≤ ∫ |f(η-ξ)|² ν(dξ)`. -/
theorem conv_sq_le (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1) (f : Lp ℂ 2 (volume : Measure (Rd d)))
    (η : Rd d) : ‖conv ν ψ f η‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν := by
  by_cases hI : ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν = ⊤
  · rw [hI]; exact le_top
  have hk := memLp_two_of_lintegral (sm_shift f η).aestronglyMeasurable hI
  have hB : ‖inner ℂ ψ (hk.toLp _)‖ ^ 2 ≤ ‖hk.toLp _‖ ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa [hψ] using norm_inner_le_norm (𝕜 := ℂ) ψ (hk.toLp _)
  rw [norm_sq_toLp] at hB
  rw [conv_eq_inner ψ hk, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_toReal hI]
  exact ENNReal.ofReal_le_ofReal hB

/-- Auxiliary: `η ↦ M_ψ f(η)` is strongly measurable. -/
theorem sm_conv [SFinite ν] (ψ : Lp ℂ 2 ν) (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    StronglyMeasurable (conv ν ψ f) := by
  have h : StronglyMeasurable (fun p : Rd d × Rd d => conj (ψ p.2) * f (p.1 - p.2)) :=
    (Complex.continuous_conj.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable ψ).comp_measurable measurable_snd)).mul (sm_shift₂ f)
  exact h.integral_prod_right'

/-- Auxiliary: the bound of `M_ψ`, `∫ |M_ψ f|² ≤ ν(ℝ^d) ∫ |f|²` for a unit `ψ`. -/
theorem convMap_bound [IsFiniteMeasure ν] (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1)
    (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    ∫⁻ η, ‖conv ν ψ f η‖ₑ ^ 2 ≤ ν univ * ∫⁻ ζ, ‖f ζ‖ₑ ^ 2 := by
  calc ∫⁻ η, ‖conv ν ψ f η‖ₑ ^ 2 ≤ ∫⁻ η, 1 * ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν :=
        lintegral_mono fun η => by rw [one_mul]; exact conv_sq_le ψ hψ f η
    _ = ∫⁻ ζ, ‖f ζ‖ₑ ^ 2 * ∫⁻ ξ, (fun _ => (1 : ℝ≥0∞)) (ζ + ξ) ∂ν :=
        lintegral_weight_shift f _ measurable_const
    _ = ν univ * ∫⁻ ζ, ‖f ζ‖ₑ ^ 2 := by
        simp only [lintegral_const, one_mul]
        rw [lintegral_mul_const _ ((Lp.stronglyMeasurable f).measurable.enorm.pow_const 2),
          mul_comm]

/-- Auxiliary: `M_ψ` is additive on `L²` classes up to null sets. -/
theorem convMap_add [IsFiniteMeasure ν] (ψ : Lp ℂ 2 ν) (f g : Lp ℂ 2 (volume : Measure (Rd d))) :
    conv ν ψ ⇑(f + g) =ᵐ[volume] conv ν ψ ⇑f + conv ν ψ ⇑g := by
  filter_upwards [ae_ae_shift_eq (ν := ν) (Lp.coeFn_add f g),
    ae_lintegral_shift_lt_top (ν := ν) f, ae_lintegral_shift_lt_top (ν := ν) g]
    with η hη hf hg
  have hkf := memLp_two_of_lintegral (sm_shift f η).aestronglyMeasurable hf.ne
  have hkg := memLp_two_of_lintegral (sm_shift g η).aestronglyMeasurable hg.ne
  simp only [Pi.add_apply, conv]
  rw [← integral_add (integrable_conj_mul ψ hkf) (integrable_conj_mul ψ hkg)]
  refine integral_congr_ae (hη.mono fun ξ hξ => ?_)
  simp only [hξ, Pi.add_apply, mul_add]

/-- Auxiliary: `M_ψ` is homogeneous on `L²` classes up to null sets. -/
theorem convMap_smul [SFinite ν] (ψ : Lp ℂ 2 ν) (c : ℂ) (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    conv ν ψ ⇑(c • f) =ᵐ[volume] c • conv ν ψ ⇑f := by
  filter_upwards [ae_ae_shift_eq (ν := ν) (Lp.coeFn_smul c f)] with η hη
  simp only [Pi.smul_apply, smul_eq_mul, conv]
  rw [← integral_const_mul]
  refine integral_congr_ae (hη.mono fun ξ hξ => ?_)
  simp only [hξ, Pi.smul_apply, smul_eq_mul]
  ring

/-- The data of `M_ψ` on `L²(dη)` for a unit `ψ ∈ L²(ν)`, `ν` finite (bound `ν(ℝ^d)`). -/
def convMap (hν : IsFiniteMeasure ν) (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1) :
    L2Map (volume : Measure (Rd d)) :=
  haveI := hν
  { F := fun f => conv ν ψ f
    C := ν univ
    C_ne_top := measure_ne_top ν univ
    meas := fun f => (sm_conv ψ f).aestronglyMeasurable
    bound := fun f => convMap_bound ψ hψ f
    add := fun f g => convMap_add ψ f g
    smul := fun c f => convMap_smul ψ c f }

/-- The operator `M_ψ` on `L²(dη)` (Fourier side of multiplication by the mode `e`). -/
def modeOp (hν : IsFiniteMeasure ν) (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1) :
    Lp ℂ 2 (volume : Measure (Rd d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Rd d)) :=
  (convMap hν ψ hψ).op

/-- `M_ψ f = ∫ conj(ψ(ξ)) f(· - ξ) ν(dξ)` a.e. -/
theorem modeOp_ae (hν : IsFiniteMeasure ν) (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1)
    (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    (modeOp hν ψ hψ f : Rd d → ℂ) =ᵐ[volume] conv ν ψ f :=
  (convMap hν ψ hψ).op_ae f

/-! ### Self-adjointness of `M_ψ` for a real mode -/

/-- Auxiliary: `∫∫ |f(η-ξ)|² ν(dξ) dη = ν(ℝ^d) ‖f‖²` (lower integrals; `ν` s-finite). -/
theorem lintegral_shift_eq [SFinite ν] (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    ∫⁻ η, ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν = (∫⁻ ζ, ‖f ζ‖ₑ ^ 2) * ν univ := by
  have h := lintegral_weight_shift (ν := ν) f (fun _ => 1) measurable_const
  simp only [one_mul, lintegral_const] at h
  rw [h, lintegral_mul_const _ ((Lp.stronglyMeasurable f).measurable.enorm.pow_const 2)]

/-- Auxiliary: `(η, ξ) ↦ |f(η-ξ)|²` is `Leb ⊗ ν`-integrable for finite `ν`. -/
theorem integrable_shift_sq [IsFiniteMeasure ν] (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    Integrable (fun p : Rd d × Rd d => ‖f (p.1 - p.2)‖ ^ 2)
      ((volume : Measure (Rd d)).prod ν) := by
  have hm := (sm_shift₂ f).aestronglyMeasurable (μ := (volume : Measure (Rd d)).prod ν)
  refine (memLp_two_iff_integrable_sq_norm hm).1 (memLp_two_of_lintegral hm ?_)
  rw [lintegral_prod _ ((sm_shift₂ f).measurable.enorm.pow_const 2).aemeasurable,
    lintegral_shift_eq]
  exact ENNReal.mul_ne_top (lintegral_Lp_ne_top f) (measure_ne_top ν univ)

/-- Auxiliary: for a finite measure `ν`, an a.e. strongly measurable function on
`ℝ^d × ℝ^d` bounded by `|ψ(ξ)| |f(η-ξ)| |g(η)|` with `ψ ∈ L²(ν)`, `f, g ∈ L²(dη)` is
`Leb ⊗ ν`-integrable (`ab ≤ a² + b²`). -/
theorem integrable_of_triple_bound [IsFiniteMeasure ν] (ψ : Lp ℂ 2 ν)
    (f g : Lp ℂ 2 (volume : Measure (Rd d))) (F : Rd d × Rd d → ℂ)
    (hF : AEStronglyMeasurable F ((volume : Measure (Rd d)).prod ν))
    (hb : ∀ p, ‖F p‖ ≤ ‖ψ p.2‖ * ‖f (p.1 - p.2)‖ * ‖g p.1‖) :
    Integrable F ((volume : Measure (Rd d)).prod ν) := by
  have hg2 : Integrable (fun η => ‖g η‖ ^ 2) (volume : Measure (Rd d)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have hψ2 : Integrable (fun ξ => ‖ψ ξ‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ψ)).1 (Lp.memLp ψ)
  have hsum := (hg2.mul_prod hψ2).add (integrable_shift_sq (ν := ν) f)
  refine hsum.mono' hF (Eventually.of_forall fun p => (hb p).trans ?_)
  simp only [Pi.add_apply]
  have h1 := norm_nonneg (ψ p.2)
  have h2 := norm_nonneg (f (p.1 - p.2))
  have h3 := norm_nonneg (g p.1)
  nlinarith [sq_nonneg (‖ψ p.2‖ * ‖g p.1‖ - ‖f (p.1 - p.2)‖), mul_nonneg h1 h3]

/-- Auxiliary: for an even `ν`, `∫ A(-ξ) ν(dξ) = ∫ A(ξ) ν(dξ)`. -/
theorem integral_comp_neg_of_even (hν : ν.map (fun x => -x) = ν) (A : Rd d → ℂ) :
    ∫ ξ, A (-ξ) ∂ν = ∫ ξ, A ξ ∂ν := by
  have he : (fun x : Rd d => -x) = ⇑(MeasurableEquiv.neg (Rd d)) := rfl
  conv_rhs => rw [← hν, he]
  rw [(MeasurableEquiv.neg (Rd d)).measurableEmbedding.integral_map]
  rfl

/-- **`M_ψ` is self-adjoint for a real mode**: if `ν` is even and `ψ(-ξ) = conj ψ(ξ)`
`ν`-a.e. (equivalently, the mode `e(x) = ∫ e^{ix·ξ} conj ψ(ξ) ν(dξ)` is real-valued), then
`M_ψ` is self-adjoint on `L²(dη)`.  Fubini, translation invariance and evenness. -/
theorem modeOp_isSelfAdjoint (hfin : IsFiniteMeasure ν) (hν : ν.map (fun x => -x) = ν)
    (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1) (hherm : ∀ᵐ ξ ∂ν, ψ (-ξ) = conj (ψ ξ)) :
    IsSelfAdjoint (modeOp hfin ψ hψ) := by
  have := hfin
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simp only [ContinuousLinearMap.coe_coe]
  rw [L2.inner_def, L2.inner_def]
  have hψm : StronglyMeasurable (fun p : Rd d × Rd d => (ψ p.2 : ℂ)) :=
    (Lp.stronglyMeasurable ψ).comp_measurable measurable_snd
  have hcm : Continuous (fun z : ℂ => conj z) := Complex.continuous_conj
  -- the two Fubini integrands
  have hF1 : Integrable (fun p : Rd d × Rd d => ψ p.2 * conj (f (p.1 - p.2)) * g p.1)
      ((volume : Measure (Rd d)).prod ν) := by
    refine integrable_of_triple_bound ψ f g _ ?_ fun p => by simp
    exact ((hψm.mul (hcm.comp_stronglyMeasurable (sm_shift₂ f))).mul
      ((Lp.stronglyMeasurable g).comp_measurable measurable_fst)).aestronglyMeasurable
  have hF3 : Integrable (fun p : Rd d × Rd d => conj (f p.1) * (conj (ψ p.2) * g (p.1 - p.2)))
      ((volume : Measure (Rd d)).prod ν) := by
    refine integrable_of_triple_bound ψ g f _ ?_ fun p => by
      simp only [norm_mul, Complex.norm_conj]; ring_nf; rfl
    exact ((hcm.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable f).comp_measurable measurable_fst)).mul
      ((hcm.comp_stronglyMeasurable hψm).mul (sm_shift₂ g))).aestronglyMeasurable
  -- left side
  have hL : ∫ η, inner ℂ (modeOp hfin ψ hψ f η) (g η) =
      ∫ η, ∫ ξ, ψ ξ * conj (f (η - ξ)) * g η ∂ν := by
    refine integral_congr_ae ((modeOp_ae hfin ψ hψ f).mono fun η hη => ?_)
    simp only
    rw [hη, RCLike.inner_apply', conv, ← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp [map_mul]
  -- right side
  have hR : ∫ ζ, inner ℂ (f ζ) (modeOp hfin ψ hψ g ζ) =
      ∫ ζ, ∫ ξ, conj (f ζ) * (conj (ψ ξ) * g (ζ - ξ)) ∂ν := by
    refine integral_congr_ae ((modeOp_ae hfin ψ hψ g).mono fun ζ hζ => ?_)
    simp only
    rw [hζ, RCLike.inner_apply', conv, ← integral_const_mul]
  rw [hL, hR, integral_integral_swap hF1,
    integral_integral_swap (f := fun ζ ξ => conj (f ζ) * (conj (ψ ξ) * g (ζ - ξ))) hF3]
  -- translate in `η`, then reflect in `ξ`
  have hT : ∀ ξ : Rd d, ∫ η, ψ ξ * conj (f (η - ξ)) * g η =
      ∫ ζ, ψ ξ * conj (f ζ) * g (ζ + ξ) := by
    intro ξ
    rw [← integral_add_right_eq_self _ ξ]
    simp
  simp_rw [hT]
  rw [← integral_comp_neg_of_even hν]
  refine integral_congr_ae (hherm.mono fun ξ hξ => ?_)
  simp only [hξ, ← sub_eq_add_neg]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only
  ring

end Conv

/-! ### `A_ρ^{-1/2}`, the band projection and the column bound -/

section Column

variable {d : ℕ}

/-- `w_ρ(η) = (ρ² + |η|²)^{-1/2}`, the Fourier multiplier of `A_ρ^{-1/2}`, `A_ρ = ρ² - Δ`. -/
def wt (ρ : ℝ) (η : Rd d) : ℝ := 1 / √(ρ ^ 2 + ‖η‖ ^ 2)

/-- Auxiliary: `w_ρ` is measurable. -/
theorem measurable_wt (ρ : ℝ) : Measurable (wt (d := d) ρ) := by
  unfold wt; fun_prop

/-- Auxiliary: `w_ρ(η)² = 1/(ρ² + |η|²)` for `ρ > 0`. -/
theorem wt_sq {ρ : ℝ} (hρ : 0 < ρ) (η : Rd d) : wt ρ η ^ 2 = 1 / (ρ ^ 2 + ‖η‖ ^ 2) := by
  rw [wt, div_pow, one_pow, Real.sq_sqrt (by positivity)]

/-- Auxiliary: `|w_ρ| ≤ ρ^{-1}` for `ρ > 0` (that is, `A_ρ ≥ ρ²`). -/
theorem abs_wt_le {ρ : ℝ} (hρ : 0 < ρ) (η : Rd d) : |wt ρ η| ≤ ρ⁻¹ := by
  have h0 : 0 ≤ wt ρ η := by unfold wt; positivity
  rw [abs_of_nonneg h0]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [wt_sq hρ, inv_pow, one_div]
  exact inv_anti₀ (by positivity) (le_add_of_nonneg_right (by positivity))

/-- The operator `A_ρ^{-1/2}` on the Fourier side `L²(dη)`: multiplication by `w_ρ`. -/
def sqrtResolvent (ρ : ℝ) (hρ : 0 < ρ) :
    Lp ℂ 2 (volume : Measure (Rd d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Rd d)) :=
  mulOp (wt ρ) (measurable_wt ρ) ρ⁻¹ (abs_wt_le hρ)

/-- The indicator of the band `|η| ≤ b`. -/
def band (b : ℝ) (η : Rd d) : ℝ := (Metric.closedBall (0 : Rd d) b).indicator (fun _ => 1) η

/-- Auxiliary: the band indicator is measurable. -/
theorem measurable_band (b : ℝ) : Measurable (band (d := d) b) :=
  measurable_const.indicator Metric.isClosed_closedBall.measurableSet

/-- Auxiliary: the band indicator is bounded by `1`. -/
theorem abs_band_le (b : ℝ) (η : Rd d) : |band b η| ≤ 1 := by
  unfold band; by_cases h : η ∈ Metric.closedBall (0 : Rd d) b <;> simp [h]

/-- The band projection `S_b` on the Fourier side: multiplication by `1_{|η| ≤ b}`. -/
def bandProj (b : ℝ) :
    Lp ℂ 2 (volume : Measure (Rd d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Rd d)) :=
  mulOp (band b) (measurable_band b) 1 (abs_band_le b)

/-- `A_ρ^{-1/2}` is self-adjoint. -/
theorem sqrtResolvent_isSelfAdjoint {ρ : ℝ} (hρ : 0 < ρ) :
    IsSelfAdjoint (sqrtResolvent (d := d) ρ hρ) :=
  mulOp_isSelfAdjoint _ _ _ _

/-- `‖A_ρ^{-1/2} f‖ ≤ ρ^{-1} ‖f‖`. -/
theorem sqrtResolvent_norm_le {ρ : ℝ} (hρ : 0 < ρ) (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    ‖sqrtResolvent ρ hρ f‖ ≤ ρ⁻¹ * ‖f‖ :=
  mulOp_norm_le _ _ _ _ (inv_nonneg.2 hρ.le) f

/-- `S_b` is self-adjoint. -/
theorem bandProj_isSelfAdjoint (b : ℝ) : IsSelfAdjoint (bandProj (d := d) b) :=
  mulOp_isSelfAdjoint _ _ _ _

/-- `S_b` is idempotent. -/
theorem bandProj_idem (b : ℝ) : bandProj (d := d) b ∘L bandProj b = bandProj b :=
  mulOp_comp _ _ _ _ _ _ _ _ _ _ _ _ fun η => by
    unfold band; by_cases h : η ∈ Metric.closedBall (0 : Rd d) b <;> simp [h]

/-- `S_b` commutes with `A_ρ^{-1/2}` (both are Fourier multipliers). -/
theorem bandProj_comm {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    bandProj (d := d) b ∘L sqrtResolvent ρ hρ = sqrtResolvent ρ hρ ∘L bandProj b := by
  have hab : ∀ η : Rd d, |band b η * wt ρ η| ≤ 1 * ρ⁻¹ := fun η => by
    rw [abs_mul]
    exact mul_le_mul (abs_band_le b η) (abs_wt_le hρ η) (abs_nonneg _) zero_le_one
  rw [bandProj, sqrtResolvent, mulOp_comp _ _ _ _ _ ((measurable_band b).mul (measurable_wt ρ))
    _ _ _ _ _ hab fun η => rfl, mulOp_comp _ _ _ _ _ ((measurable_band b).mul (measurable_wt ρ))
    _ _ _ _ _ hab fun η => mul_comm _ _]

variable {ν : Measure (Rd d)}

/-- Auxiliary: `|w_ρ(η)|² = 1/(ρ² + |η|²)` as an extended real. -/
theorem enorm_wt_sq {ρ : ℝ} (hρ : 0 < ρ) (η : Rd d) :
    ‖(wt ρ η : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (1 / (ρ ^ 2 + ‖η‖ ^ 2)) := by
  rw [← ofReal_norm, Complex.norm_real, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
    sq_abs, wt_sq hρ]

/-- **The column bound `E:interval-column` on the concrete model** (main TeX lines 3388-3391;
proof 3406-3442 at edf7085f, there with the full mode family): for a finite measure `ν`, an
orthonormal family `ψ_1, …, ψ_m` in `L²(ν)`, `ρ > 0` and `c ≥ 0` with the resolvent bound
`∫ ν(dξ)/(ρ² + |q+ξ|²) ≤ c` for all `q`,
`∑_i ‖A_ρ^{-1/2} M_{ψ_i} f‖² ≤ c ‖f‖²` on `L²(dη)`.  Proof: Bessel's inequality in
`L²(ν)` at each `η` (`sum_conv_le`), then Tonelli and translation invariance
(`lintegral_weight_shift`), then the resolvent bound. -/
theorem column_bound (hfin : IsFiniteMeasure ν) {m : ℕ} (ψ : Fin m → Lp ℂ 2 ν)
    (hψ : Orthonormal ℂ ψ) {ρ c : ℝ} (hρ : 0 < ρ) (hc0 : 0 ≤ c)
    (hres : ∀ q : Rd d, ∫⁻ ξ, ENNReal.ofReal (1 / (ρ ^ 2 + ‖q + ξ‖ ^ 2)) ∂ν ≤ ENNReal.ofReal c) :
    FockForm.FockColumn (fun i => sqrtResolvent ρ hρ ∘L modeOp hfin (ψ i) (hψ.1 i)) c := by
  have := hfin
  intro u
  set W : Rd d → ℝ≥0∞ := fun η => ENNReal.ofReal (1 / (ρ ^ 2 + ‖η‖ ^ 2)) with hWdef
  have hW : Measurable W := by rw [hWdef]; fun_prop
  set I : Fin m → ℝ≥0∞ := fun i => ∫⁻ η, W η * ‖conv ν (ψ i) u η‖ₑ ^ 2 with hIdef
  have hnorm : ∀ i, ‖(sqrtResolvent ρ hρ ∘L modeOp hfin (ψ i) (hψ.1 i)) u‖ ^ 2 = (I i).toReal := by
    intro i
    rw [ContinuousLinearMap.comp_apply, norm_sq_Lp]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [mulOp_ae (μ := (volume : Measure (Rd d))) (wt ρ) (measurable_wt ρ) ρ⁻¹
      (abs_wt_le hρ) (modeOp hfin (ψ i) (hψ.1 i) u), modeOp_ae hfin (ψ i) (hψ.1 i) u]
      with η h1 h2
    rw [sqrtResolvent, h1, h2, enorm_mul, mul_pow, enorm_wt_sq hρ]
  have hsum : ∑ i, I i ≤ ENNReal.ofReal c * ∫⁻ ζ, ‖u ζ‖ₑ ^ 2 := by
    calc ∑ i, I i = ∫⁻ η, ∑ i, W η * ‖conv ν (ψ i) u η‖ₑ ^ 2 := by
          rw [lintegral_finsetSum]
          intro i _
          exact hW.mul ((sm_conv (ψ i) u).measurable.enorm.pow_const 2)
      _ ≤ ∫⁻ η, W η * ∫⁻ ξ, ‖u (η - ξ)‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun η => ?_
          rw [← Finset.mul_sum]
          gcongr
          exact sum_conv_le ψ hψ u η
      _ = ∫⁻ ζ, ‖u ζ‖ₑ ^ 2 * ∫⁻ ξ, W (ζ + ξ) ∂ν := lintegral_weight_shift u W hW
      _ ≤ ∫⁻ ζ, ‖u ζ‖ₑ ^ 2 * ENNReal.ofReal c :=
          lintegral_mono fun ζ => by gcongr; exact hres ζ
      _ = ENNReal.ofReal c * ∫⁻ ζ, ‖u ζ‖ₑ ^ 2 := by
          rw [lintegral_mul_const _ ((Lp.stronglyMeasurable u).measurable.enorm.pow_const 2),
            mul_comm]
  have hfin' : ENNReal.ofReal c * ∫⁻ ζ, ‖u ζ‖ₑ ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_Lp_ne_top u)
  simp_rw [hnorm]
  rw [← ENNReal.toReal_sum fun i _ => ne_top_of_le_ne_top hfin'
    ((Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans hsum)]
  calc (∑ i, I i).toReal ≤ (ENNReal.ofReal c * ∫⁻ ζ, ‖u ζ‖ₑ ^ 2).toReal :=
        ENNReal.toReal_mono hfin' hsum
    _ = c * ‖u‖ ^ 2 := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0, norm_sq_Lp]

/-- **Substitution** (main TeX lines 3455-3459): for `c ≥ 0`, from the column bound `c` for
`A_ρ^{-1/2} M_{ψ_i}`, the sandwiches `A_ρ^{-1/2} M_{ψ_i} A_ρ^{-1/2}` have column bound
`c ρ^{-2}`. -/
theorem column_sandwich (hfin : IsFiniteMeasure ν) {m : ℕ} (ψ : Fin m → Lp ℂ 2 ν)
    (hψ : Orthonormal ℂ ψ) {ρ c : ℝ} (hρ : 0 < ρ) (hc0 : 0 ≤ c)
    (hcol : FockForm.FockColumn (fun i => sqrtResolvent ρ hρ ∘L modeOp hfin (ψ i) (hψ.1 i)) c) :
    FockForm.FockColumn
      (fun i => sqrtResolvent ρ hρ ∘L modeOp hfin (ψ i) (hψ.1 i) ∘L sqrtResolvent ρ hρ)
      (c * ρ⁻¹ ^ 2) := by
  intro u
  calc ∑ i, ‖(sqrtResolvent ρ hρ ∘L modeOp hfin (ψ i) (hψ.1 i) ∘L sqrtResolvent ρ hρ) u‖ ^ 2
      = ∑ i, ‖(sqrtResolvent ρ hρ ∘L modeOp hfin (ψ i) (hψ.1 i)) (sqrtResolvent ρ hρ u)‖ ^ 2 :=
        rfl
    _ ≤ c * ‖sqrtResolvent ρ hρ u‖ ^ 2 := hcol _
    _ ≤ c * (ρ⁻¹ * ‖u‖) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (sqrtResolvent_norm_le hρ u) 2) hc0
    _ = c * ρ⁻¹ ^ 2 * ‖u‖ ^ 2 := by ring

end Column

/-! ### The smoothed spectral measure and the concrete modes -/

section Concrete

variable {d : ℕ}

open HomogHypothesis (IsTempered IsEven IsSpectralMeasure HomogCovariance)
open SpectralHomog (SpectralHomogeneous)
open SpectralMassIdentity (ralpha)
open HermiteFock (Supp degLE fieldOp iota)

/-- The spectral measure `μ_ε(dξ) = e^{-ε|ξ|²} μ(dξ)` of the smoothed covariance
`Γ_ε = p_{2ε} * Γ` (main TeX lines 2505-2506 and 3392-3394 at edf7085f; the factor
`e^{-ε|ξ|²}` is the one in `J_{ρ,ε}`, lines 2995-2999). -/
def nuEps (μ : Measure (Rd d)) (ε : ℝ) : Measure (Rd d) :=
  μ.withDensity fun ξ => ENNReal.ofReal (Real.exp (-(ε * ‖ξ‖ ^ 2)))

/-- `μ_ε` is finite for a tempered `μ` and `ε > 0`. -/
theorem nuEps_finite {μ : Measure (Rd d)} (hμt : IsTempered μ) {ε : ℝ} (hε : 0 < ε) :
    IsFiniteMeasure (nuEps μ ε) := by
  have h := MaskedSpectralGrowth.integrable_gauss_of_tempered hμt hε (0 : Rd d)
  simp only [sub_zero] at h
  exact isFiniteMeasure_withDensity_ofReal h.2

/-- `μ_ε` is even when `μ` is. -/
theorem nuEps_even {μ : Measure (Rd d)} (hμe : IsEven μ) (ε : ℝ) :
    (nuEps μ ε).map (fun x => -x) = nuEps μ ε := by
  have hf : Measurable (fun ξ : Rd d => ENNReal.ofReal (Real.exp (-(ε * ‖ξ‖ ^ 2)))) := by
    fun_prop
  ext s hs
  rw [Measure.map_apply measurable_neg hs, nuEps, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  conv_rhs => rw [← hμe]
  rw [setLIntegral_map hs hf measurable_neg]
  simp [norm_neg]

/-- **`E:phase-resolvent` for `μ_ε`** (main TeX lines 2512-2514, and its `d`-dimensional
form at lines 3416-3430): `∫ μ_ε(dξ)/(ρ² + |q+ξ|²) ≤ R_α ρ^{α-2}`, from
`PhaseContractions.phase_resolvent` and `e^{-ε|ξ|²} ≤ 1`. -/
theorem nuEps_resolvent {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure μ] {alpha : ℝ}
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    {ε : ℝ} (hε : 0 ≤ ε) {ρ : ℝ} (hρ : 0 < ρ) (q : Rd d) :
    ∫⁻ ξ, ENNReal.ofReal (1 / (ρ ^ 2 + ‖q + ξ‖ ^ 2)) ∂(nuEps μ ε) ≤
      ENNReal.ofReal (ralpha μ alpha * ρ ^ (alpha - 2)) := by
  obtain ⟨hint, hle, -⟩ := PhaseContractions.phase_resolvent hμt hsp hΓs ha0 ha2 ρ hρ q
  rw [nuEps, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  calc ∫⁻ ξ, ((fun ξ : Rd d => ENNReal.ofReal (Real.exp (-(ε * ‖ξ‖ ^ 2)))) *
        fun ξ => ENNReal.ofReal (1 / (ρ ^ 2 + ‖q + ξ‖ ^ 2))) ξ ∂μ
      ≤ ∫⁻ ξ, ENNReal.ofReal (1 / (ρ ^ 2 + ‖q + ξ‖ ^ 2)) ∂μ := by
        refine lintegral_mono fun ξ => ?_
        simp only [Pi.mul_apply]
        calc ENNReal.ofReal (Real.exp (-(ε * ‖ξ‖ ^ 2))) *
              ENNReal.ofReal (1 / (ρ ^ 2 + ‖q + ξ‖ ^ 2))
            ≤ 1 * ENNReal.ofReal (1 / (ρ ^ 2 + ‖q + ξ‖ ^ 2)) := by
              gcongr
              exact ENNReal.ofReal_le_one.2
                (Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity)))
          _ = _ := one_mul _
    _ = ENNReal.ofReal (∫ ξ, 1 / (ρ ^ 2 + ‖q + ξ‖ ^ 2) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun ξ => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

/-- The concrete mode operators `M_{e_i}` (Fourier side) of an orthonormal family `ψ` in
`L²(ν)`, `ν` finite. -/
def modes {ν : Measure (Rd d)} (hfin : IsFiniteMeasure ν) {m : ℕ} (ψ : Fin m → Lp ℂ 2 ν)
    (hψ : Orthonormal ℂ ψ) (i : Fin m) :
    Lp ℂ 2 (volume : Measure (Rd d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Rd d)) :=
  modeOp hfin (ψ i) (hψ.1 i)

/-- Auxiliary: `R_α ρ^{α-2} ρ^{-2} = R_α ρ^{α-4}`. -/
theorem rpow_sub_two_mul_inv_sq (R alpha : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    R * ρ ^ (alpha - 2) * ρ⁻¹ ^ 2 = R * ρ ^ (alpha - 4) := by
  rw [mul_assoc, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
  congr 2; push_cast; ring

/-! ### The completed wrappers -/

/-- **`E:interval-column` on the concrete model, under `H:homog`** (main TeX lines 3388-3391,
proof 3416-3445 at edf7085f): for `ε, ρ > 0` and an orthonormal family `ψ_1, …, ψ_m` in
`L²(μ_ε)`, `∑_i ‖A_ρ^{-1/2} M_{e_i} f‖² ≤ R_α ρ^{α-2} ‖f‖²` on the Fourier side `L²(dη)`.
The `FockColumn` input of `FockForm.interval_contractions_paper`, proved. -/
theorem interval_column_completed {d : ℕ} {alpha alpha0 R ε ρ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (hρ : 0 < ρ) {m : ℕ} (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) :
    FockForm.FockColumn
      (fun i => sqrtResolvent ρ hρ ∘L modes (nuEps_finite hH.μ_tempered hε) ψ hψ i)
      (R * ρ ^ (alpha - 2)) := by
  have := hH.μ_radon
  have hα0 : 0 < alpha := by
    rcases hH.alpha_range with h | h
    · exact h.1
    · rw [h.1]; rcases h.2 with rfl; norm_num
  have hα2 : alpha < 2 := by linarith [hH.threshold, hH.alpha0_pos]
  have hR0 : 0 ≤ R := hRdef ▸ IntervalScalar.ralpha_nonneg μ hα0 hα2
  have hRr : R = ralpha μ alpha := hRdef
  refine column_bound (nuEps_finite hH.μ_tempered hε) ψ hψ hρ
    (mul_nonneg hR0 (Real.rpow_nonneg hρ.le _)) fun q => ?_
  rw [hRr]
  exact nuEps_resolvent hH.μ_tempered hH.spectral hH.scaling hα0 hα2 hε.le hρ q

/-- **The spatial half of `L:fock-form` on the concrete model** (main TeX lines 2987-3008 at
edf7085f): under the class of `S:static-phase` (`PhaseCovariance`), for `ε, ρ > 0` and an
orthonormal family `ψ_1, …, ψ_m` in `L²(μ_ε)` of real modes (`ψ_i(-ξ) = conj ψ_i(ξ)`
`μ_ε`-a.e.), the sandwiches `H_i = A_ρ^{-1/2} M_{e_i} A_ρ^{-1/2}` are self-adjoint and
`∑_i ‖H_i f‖² ≤ R_α ρ^{α-4} ‖f‖²`. -/
theorem fock_column_completed {alpha R ε ρ : ℝ} {Γ μ : Measure (Rd 3)}
    (hPC : PhaseContractions.PhaseCovariance alpha Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (hρ : 0 < ρ) {m : ℕ} (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ)) :
    (∀ i, IsSelfAdjoint (sqrtResolvent ρ hρ ∘L
        modes (nuEps_finite hPC.μ_tempered hε) ψ hψ i ∘L sqrtResolvent ρ hρ)) ∧
      FockForm.FockColumn (fun i => sqrtResolvent ρ hρ ∘L
        modes (nuEps_finite hPC.μ_tempered hε) ψ hψ i ∘L sqrtResolvent ρ hρ)
        (R * ρ ^ (alpha - 4)) := by
  have := hPC.μ_radon
  have hR0 : 0 ≤ R := hRdef ▸ IntervalScalar.ralpha_nonneg μ hPC.alpha_pos hPC.alpha_lt_two
  have hRr : R = ralpha μ alpha := hRdef
  have hfin := nuEps_finite hPC.μ_tempered hε
  have hc0 : 0 ≤ R * ρ ^ (alpha - 2) := mul_nonneg hR0 (Real.rpow_nonneg hρ.le _)
  have hcol : FockForm.FockColumn (fun i => sqrtResolvent ρ hρ ∘L modes hfin ψ hψ i)
      (R * ρ ^ (alpha - 2)) := by
    refine column_bound hfin ψ hψ hρ hc0 fun q => ?_
    rw [hRr]
    exact nuEps_resolvent hPC.μ_tempered hPC.spectral hPC.scaling' hPC.alpha_pos
      hPC.alpha_lt_two hε.le hρ q
  refine ⟨fun i => ?_, ?_⟩
  · have hS := sqrtResolvent_isSelfAdjoint (d := 3) hρ
    have h := (modeOp_isSelfAdjoint hfin (nuEps_even hPC.μ_even ε) (ψ i) (hψ.1 i)
      (hreal i)).conjugate (sqrtResolvent ρ hρ)
    rw [hS.star_eq] at h
    exact h
  · rw [← rpow_sub_two_mul_inv_sq R alpha hρ]
    exact column_sandwich hfin ψ hψ hρ hc0 hcol

/-- **`L:fock-form` on the concrete model, with the spatial half proved** (main TeX lines
2960-2977, proof 2979-3028 at edf7085f).  `FockForm.fock_form_paper` for `X = L²(dη)` (the
Fourier side of spatial `L²(ℝ³)`), `H_i = A_ρ^{-1/2} M_{e_i} A_ρ^{-1/2}` built from an
orthonormal family of real modes `ψ_i ∈ L²(μ_ε)`, and the band projection `P = S_b`
(`bandProj b`, `|η| ≤ b`), with the inputs `hH` (self-adjointness), `hcol` (`FockColumn`),
`hP` and `hPP` discharged (`fock_column_completed`, `bandProj_isSelfAdjoint`,
`bandProj_idem`).  Standing assumptions: `PhaseCovariance` (the class of `S:static-phase`,
lines 2490-2493), `R = R_α`, `ε, ρ > 0`.  Conclusion: for every `N` and coefficient vector
`v` of Hermite degree `≤ N`, `B = P_N (∑_i g_i ⊗ S_b H_i S_b) P_N` has norm at most
`d_N ρ^{α/2-2}` on the coefficient model and in Gaussian `L²`, and is symmetric. -/
theorem fock_form_paper_completed {alpha R ε ρ b : ℝ} {Γ μ : Measure (Rd 3)}
    (hPC : PhaseContractions.PhaseCovariance alpha Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (hρ : 0 < ρ) {m : ℕ} (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ))
    (N : ℕ) {v : (Fin m → ℕ) → Lp ℂ 2 (volume : Measure (Rd 3))} (hv : Supp N v) :
    let H := fun i => sqrtResolvent ρ hρ ∘L
      modes (nuEps_finite hPC.μ_tempered hε) ψ hψ i ∘L sqrtResolvent ρ hρ
    let P := bandProj (d := 3) b
    ∑ k ∈ degLE m N, ‖fieldOp (fun i => P ∘L H i ∘L P) v k‖ ^ 2 ≤
        (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 * ∑ k ∈ degLE m N, ‖v k‖ ^ 2 ∧
      Integrable (fun x => ‖iota N (fieldOp (fun i => P ∘L H i ∘L P) v) x‖ ^ 2)
        (GaussianIBP.stdPi m) ∧
      ∫ x, ‖iota N (fieldOp (fun i => P ∘L H i ∘L P) v) x‖ ^ 2 ∂GaussianIBP.stdPi m ≤
        (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
          ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m ∧
      ∀ w : (Fin m → ℕ) → Lp ℂ 2 (volume : Measure (Rd 3)), Supp N w →
        ∑ k ∈ degLE m N, inner ℂ (fieldOp (fun i => P ∘L H i ∘L P) v k) (w k) =
          ∑ k ∈ degLE m N, inner ℂ (v k) (fieldOp (fun i => P ∘L H i ∘L P) w k) := by
  intro H P
  obtain ⟨hHs, hcol⟩ := fock_column_completed hPC hRdef hε hρ ψ hψ hreal
  exact FockForm.fock_form_paper Γ μ hPC.Γ_radon hPC.μ_radon hPC.Γ_even hPC.Γ_tempered
    hPC.Γ_posdef hPC.spectral hPC.scaling hPC.alpha_pos hPC.alpha_lt_two hRdef hε hρ H hHs hcol
    P (bandProj_isSelfAdjoint b) (bandProj_idem b) N hv

/-- **`L:interval-contractions` on the concrete model, with `E:interval-column` proved**
(main TeX lines 3384-3404, proof 3406-3470 at edf7085f).
`FockForm.interval_contractions_paper` for `X = L²(dη)` (the Fourier side of spatial
`L²(ℝ^d)`), `S = A_ρ^{-1/2}` (`sqrtResolvent ρ`), `M_i = M_{e_i}` built from an orthonormal
family of real modes `ψ_i ∈ L²(μ_ε)`, and `P = S_b` (`bandProj b`), with every operator input
discharged: `hS`, `hSn`, `hM`, `hcol` (`E:interval-column`, `interval_column_completed`),
`hP`, `hPP`, `hPS`.  Standing assumptions: `H:homog`, `R = R_α`, `ε, ρ > 0`.  Conclusions
(a)-(d) of `FockForm.interval_contractions`. -/
theorem interval_contractions_paper_completed {d : ℕ} {alpha alpha0 R ε ρ b : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (hρ : 0 < ρ) {m : ℕ} (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ)) :
    let S := sqrtResolvent (d := d) ρ hρ
    let M := modes (nuEps_finite hH.μ_tempered hε) ψ hψ
    let P := bandProj (d := d) b
    FockForm.FockColumn (fun i => S ∘L (P ∘L M i ∘L P)) (R * ρ ^ (alpha - 2)) ∧
      (∀ u w : Lp ℂ 2 (volume : Measure (Rd d)),
        Integrable (fun x => ‖∑ i, ((x i : ℝ) : ℂ) • (S ∘L (P ∘L M i ∘L P)) u‖ ^ 2)
          (GaussianIBP.stdPi m) ∧
        ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • (S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ∂GaussianIBP.stdPi m =
          ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ∧
        ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ≤ R * ρ ^ (alpha - 2) * (‖u‖ ^ 2 + ‖S w‖ ^ 2)) ∧
      (∀ i, IsSelfAdjoint (S ∘L (P ∘L M i ∘L P) ∘L S)) ∧
      FockForm.FockColumn (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) (R * ρ ^ (alpha - 4)) ∧
      ∀ (N : ℕ) (v : (Fin m → ℕ) → Lp ℂ 2 (volume : Measure (Rd d))), Supp N v →
        ∑ k ∈ degLE m N, ‖fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v k‖ ^ 2 ≤
          (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
            ∑ k ∈ degLE m N, ‖v k‖ ^ 2 ∧
        Integrable (fun x => ‖iota N (fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v) x‖ ^ 2)
          (GaussianIBP.stdPi m) ∧
        ∫ x, ‖iota N (fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v) x‖ ^ 2
            ∂GaussianIBP.stdPi m ≤
          (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
            ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m := by
  intro S M P
  exact FockForm.interval_contractions_paper hH hRdef hε hρ S (sqrtResolvent_isSelfAdjoint hρ)
    (sqrtResolvent_norm_le hρ) M
    (fun i => modeOp_isSelfAdjoint _ (nuEps_even hH.μ_even ε) (ψ i) (hψ.1 i) (hreal i))
    (interval_column_completed hH hRdef hε hρ ψ hψ) P (bandProj_isSelfAdjoint b)
    (bandProj_idem b) (bandProj_comm hρ b)

end Concrete

end StratonovichHAMSecondMoment.FockColumnBound
