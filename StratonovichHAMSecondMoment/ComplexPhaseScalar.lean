module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Scalar steps of `L:complex-phase` (A complex phase bound) and of
`L:interval-complex` (Complex sums and changing phase weights) of
`notes/notes_stratonovich_ham_second_moment.tex` (main TeX file; line numbers
at revision a284420).  `L:complex-phase`: statement lines 2288-2310, proof
2312-2465.  `L:interval-complex`: statement lines 2899-2917, proof 2919-2982.

Class: inputs supplied, conclusion weaker than the labelled statements.  Both
lemmas are statements about the phase propagator `M_z(h)` of `u'' + L u = 0` on
`X_λ`; this module formalizes the scalar, numerical-range and Banach-algebra
deductions of their proofs.  The propagator itself, its identification with the
weighted block matrix of functional-calculus operators, and the operator
functional calculus are not formalized.

Formalized (nothing supplied):
* the constants: `1 - δ_a ≥ 3/4`, `δ_a I_a ≤ π/8`, `4δ²/(1-δ) ≤ 1/3`,
  `1 + (1-δ)⁻¹ ≤ 7/3`, and the prefactor bound
  `c λ^{a-2} I_a/(π(1-δ_a)) ≤ 1/6` (lines 2355-2359, 2389-2393, 2424-2426);
* the scalar resolvent integral
  `∫_0^∞ t^{-1/2}(λ²+t)^{(a-3)/2} dt = λ^{a-2} I_a`, with integrability, and the
  resulting operator-norm bound for any integrand dominated as at lines
  2349-2354 (`kappa_integral`, `resolvent_integral_le`, `q_sub_one_le`);
* the Neumann bounds: `‖K‖ ≤ δ < 1` gives `‖(1-K)⁻¹‖ ≤ (1-δ)⁻¹`, and
  `‖Q - 1‖ ≤ 1/6` gives `‖Q‖ ≤ 7/6`, `Q` invertible, `‖Q⁻¹‖ ≤ 6/5`
  (lines 2320-2325, 2361, 2939-2940), in any complete normed ring with
  `‖1‖ ≤ 1`; the resolvent-difference identity of lines 2341-2348 and
  2930-2934 in any ring (`resolvent_difference`), and the four-factor norm
  product of lines 2349-2354 (`integrand_factor_le`);
* the form consequence of `E:abstract-sandwich`,
  `|⟨Bu,u⟩| ≤ c(ρ²‖u‖² + ⟨A_0u,u⟩)` when
  `‖A_ρ^{-1/2} B A_ρ^{-1/2}‖ ≤ c` (used without comment at lines 2374-2381 and
  2948-2954), for bounded operators on a complex Hilbert space, with
  `A_ρ^{-1/2}` the inverse of the continuous-functional-calculus square root
  `CFC.sqrt (A_0 + ρ²)` (`form_of_sandwich`); the adjoint sandwich identity of
  lines 2920-2924 (`sandwich_adjoint_norm`);
* the numerical-range parabola (lines 2373-2396 and 2948-2958): the
  optimization at `ρ = s` including `s = 0` by `ρ ↓ 0` (`form_opt_le`), the two
  inequalities `x + λ² ≥ (1-δ)(s²+λ²)`, `|y| ≤ 2δλ^{2-a}s^a`, the parabola
  `y² ≤ (4δ²/(1-δ)) λ²(x+λ²) ≤ λ²(x+λ²)/3`, `x ≥ -λ²/4`, `|w| ≤ x + 2λ²`, and
  `|Im r| ≤ λ` for EVERY square root `r` of `w` (`parabola`,
  `norm_le_of_parabola`, `im_root_le`);
* the scalar bounds of lines 2398-2429 on the numerical range:
  `|C_h| ≤ e^{λh}`, `|F_h| ≤ 2(1+λh)e^{λh}` (through the two cases
  `√(3/2) λh e^{λh}` and `√3 e^{λh}`), `|H_h| ≤ 2e^{λh}` (through
  `|w|/|w+λ²| ≤ 7/3`), with the removable values at `w = 0`;
* the constants of the assembly (lines 2430-2460): `(1+√2) ≤ 3`, the four block
  norms `3, 12(1+λh), 12, 12` (times `e^{λh}`) and
  `(39+12λh)e^{λh} ≤ 39(1+λh)e^{λh} ≤ 100e^{2λh}`, and the bound of a 2×2 block
  operator on `H ⊕ H` (ℓ² norm) by the sum of its four block norms;
* the `L:interval-complex` INSTANCE of `E:interval-metric` (lines 2966-2981):
  the multiplier form of `‖z‖_{ρ_new} ≤ max{1, ρ_old/ρ_new}‖z‖_{ρ_old}`, the
  jump ratio `≤ 1 + Σ_E ω_i/λ ≤ ∏_E (1+ω_i/λ)`, and the product over jumps
  whose ending sets are pairwise disjoint (each connected interval ends once).
  The general telescoping lemma for the interval metric along a time partition
  (composition with the segment propagators) is NOT proved here (it belongs to
  wave L10-FS0).

Supplied (named hypotheses of the wrappers, not formalized):
* Crouzeix-Palencia `E:cp-input` (lines 2277-2286), imported in the TeX: for
  each of `C_h, F_h, H_h` an operator `Cop, Fop, Hop` (the functional-calculus
  value at `L`) with `‖Op‖ ≤ (1+√2) M` whenever the scalar function is bounded
  by `M` on the numerical range `W(L)` (`hCPC`, `hCPF`, `hCPH`).  This is
  `E:cp-input` with its holomorphy precondition (lines 2405-2407) discharged by
  the supplier.
* The inverse-root integral representation of lines 2329-2348 (for the operator
  `L^* = A_0 - \bar z B`, resp. `A_0 - V^*`, whose adjoint gives the
  comparisons used in the blocks): an operator `Q'` with
  `Q' - 1 = π⁻¹ ∫_0^∞ J(t) dt`, `J` strongly measurable and
  `‖J(t)‖ ≤ (c/(1-δ_a)) t^{-1/2} κ^{a-3}`, `κ = (λ²+t)^{1/2}`, with
  `c = |z| d` (resp. `D`) (`hJm`, `hJ`, `hQ'`): the four-factor bound of lines
  2349-2354 and the bounded holomorphic calculus.
* The identification of the propagator `M_z(h)` in `X_λ` with the weighted
  block map of lines 2433-2444 (and 2959-2962); the wrappers conclude the bound
  for that block map, built from `Cop, Fop, Hop` and the comparisons
  `P1 = Q'^*`, `P2 = (Q'^{-1})^*` (lines 2361-2369, 2940-2946).

Narrower than the TeX: the propagator bound `E:complex-phase-bound` is concluded
for the supplied block map, not for `M_z(h)`; the comparisons with `L` itself
(`Q`, `Q^{-1}`) are bounded by the same lemma `neumann_root_comparison` but not
named in the wrappers; `s` is `√⟨A_0u,u⟩` (which is `‖A_0^{1/2}u‖`, not
restated); the interval metric is the instance described above.

Junk values: `δ_a` is a genuine positive number (`StaticPhaseCauchy.deltaA_pos`);
`A_ρ^{-1/2}` is `Ring.inverse` of a square root PROVED invertible for `ρ > 0`
(`sqrtShift_isUnit`), so the sandwich hypothesis is not vacuous; `Ring.inverse Q'`
is used only after `Q'` is proved invertible; the removable values at `w = 0` are
written as `if` branches with the correct limits (`G_h(0) = h`, `H_h(0) = 0`);
divisions by `√(w+λ²)` occur only where `Re(w+λ²) > 0` is proved; the Bochner
integral in `hQ'` is accompanied by a proof of integrability
(`resolvent_integral_le`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.StaticPhaseCauchy

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real Set MeasureTheory Filter Topology

namespace StratonovichHAMSecondMoment.ComplexPhaseScalar

open StratonovichHAMSecondMoment.StaticPhaseCauchy

/-! ## Constants -/

/-- `1 - δ_a ≥ 3/4` (from `δ_a ≤ 1/4`, the definition at main TeX line 2299). -/
theorem one_sub_deltaA_ge (a : ℝ) : 3 / 4 ≤ 1 - deltaA a := by
  have := deltaA_le_quarter a
  linarith

/-- `δ_a I_a ≤ π/8` (from `δ_a ≤ π/(8 I_a)`, main TeX line 2299). -/
theorem deltaA_mul_phaseI_le {a : ℝ} (ha : a < 2) : deltaA a * phaseI a ≤ π / 8 := by
  have hI := phaseI_pos ha
  have h : deltaA a ≤ π / (8 * phaseI a) := min_le_right _ _
  calc deltaA a * phaseI a ≤ π / (8 * phaseI a) * phaseI a := by gcongr
    _ = π / 8 := by field_simp

/-- Auxiliary (Lean route): `λ^{2-a} λ^{a-2} = 1` for `λ > 0`. -/
theorem rpow_two_sub_mul {a lam : ℝ} (hlam : 0 < lam) : lam ^ (2 - a) * lam ^ (a - 2) = 1 := by
  rw [← Real.rpow_add hlam]
  norm_num

/-- The coupling condition in the form used by the prefactor: if
`c ≤ δ λ^{2-a}` then `c λ^{a-2} ≤ δ`.  With `c = |z| d` this is
`|z| ≤ δ_a λ^{2-a}/d` (main TeX line 2301); with `c = D` it is
`D ≤ δ_a Λ^{2-a}` (line 2907). -/
theorem coeff_le_of_le {a lam c δ : ℝ} (hlam : 0 < lam) (hc : c ≤ δ * lam ^ (2 - a)) :
    c * lam ^ (a - 2) ≤ δ := by
  have hp : 0 < lam ^ (a - 2) := Real.rpow_pos_of_pos hlam _
  calc c * lam ^ (a - 2) ≤ δ * lam ^ (2 - a) * lam ^ (a - 2) := by gcongr
    _ = δ := by rw [mul_assoc, rpow_two_sub_mul hlam, mul_one]

/-- `‖z K_κ‖ ≤ δ` "since `a - 2 < 0`" (main TeX line 2320): for `κ ≥ λ > 0`,
`c κ^{a-2} ≤ c λ^{a-2}`. -/
theorem kappa_coeff_le {a lam κ c : ℝ} (ha : a ≤ 2) (hlam : 0 < lam) (hκ : lam ≤ κ) (hc : 0 ≤ c) :
    c * κ ^ (a - 2) ≤ c * lam ^ (a - 2) :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlam hκ (by linarith)) hc

/-- The prefactor bound `|z| d λ^{a-2} I_a/(π(1-δ)) ≤ 1/6` of main TeX lines
2357-2359 (and its use at lines 2936-2937), for any `c` with
`c λ^{a-2} ≤ δ_a`. -/
theorem neumann_prefactor_le {a lam c : ℝ} (ha : a < 2)
    (hcδ : c * lam ^ (a - 2) ≤ deltaA a) :
    c * lam ^ (a - 2) * phaseI a / (π * (1 - deltaA a)) ≤ 1 / 6 := by
  have hI := phaseI_pos ha
  have h1 := one_sub_deltaA_ge a
  have h2 := deltaA_mul_phaseI_le ha
  have hpos : 0 < π * (1 - deltaA a) := mul_pos pi_pos (by linarith)
  rw [div_le_iff₀ hpos]
  calc c * lam ^ (a - 2) * phaseI a ≤ deltaA a * phaseI a := by gcongr
    _ ≤ π / 8 := h2
    _ ≤ 1 / 6 * (π * (1 - deltaA a)) := by nlinarith [pi_pos]

/-- `4δ²/(1-δ) ≤ 1/3` for `0 ≤ δ ≤ 1/4` (main TeX lines 2391-2392). -/
theorem parabola_coeff_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) :
    4 * δ ^ 2 / (1 - δ) ≤ 1 / 3 := by
  have hpos : 0 < 1 - δ := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hδ hδ0]

/-- `1 + (1-δ)⁻¹ ≤ 7/3` for `δ ≤ 1/4` (main TeX line 2426). -/
theorem range_ratio_const_le {δ : ℝ} (hδ : δ ≤ 1 / 4) : 1 + (1 - δ)⁻¹ ≤ 7 / 3 := by
  have hpos : 0 < 1 - δ := by linarith
  have : (1 - δ)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  linarith

/-! ## The scalar resolvent integral (main TeX lines 2329-2359) -/

/-- Auxiliary (Lean route): the scaling `t = λ² s` of the integrand,
`g(λ²s) = λ^{a-4} s^{-1/2}(1+s)^{(a-3)/2}` for `s > 0`. -/
theorem kappa_integrand_scale {a lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) :
    (lam ^ 2 * s) ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + lam ^ 2 * s) ^ ((a - 3) / 2) =
      lam ^ (a - 4) * (s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2)) := by
  have hl2 : (0 : ℝ) ≤ lam ^ 2 := sq_nonneg _
  have hpow : ∀ p : ℝ, (lam ^ 2) ^ p = lam ^ (2 * p) := by
    intro p
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
  have e1 : lam ^ 2 + lam ^ 2 * s = lam ^ 2 * (1 + s) := by ring
  rw [e1, Real.mul_rpow hl2 hs.le, Real.mul_rpow hl2 (by linarith), hpow, hpow]
  have e2 : lam ^ (2 * (-(1 / 2 : ℝ))) * lam ^ (2 * ((a - 3) / 2)) = lam ^ (a - 4) := by
    rw [← Real.rpow_add hlam]
    congr 1
    ring
  calc lam ^ (2 * (-(1 / 2 : ℝ))) * s ^ (-(1 / 2 : ℝ)) *
        (lam ^ (2 * ((a - 3) / 2)) * (1 + s) ^ ((a - 3) / 2))
        = (lam ^ (2 * (-(1 / 2 : ℝ))) * lam ^ (2 * ((a - 3) / 2))) *
          (s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2)) := by ring
    _ = _ := by rw [e2]

/-- The scalar resolvent integral of main TeX lines 2355-2358: with
`κ = (λ²+t)^{1/2}`, so that `κ^{a-3} = (λ²+t)^{(a-3)/2}` (`kappa_rpow_eq`),
`∫_0^∞ t^{-1/2} κ^{a-3} dt = λ^{a-2} I_a`, with integrability (for `a < 2`,
`λ > 0`). -/
theorem kappa_integral {a lam : ℝ} (ha : a < 2) (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2) =
        lam ^ (a - 2) * phaseI a := by
  set g : ℝ → ℝ := fun t => t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2) with hg
  have hl2 : 0 < lam ^ 2 := by positivity
  have hEq : EqOn (fun s => g (lam ^ 2 * s))
      (fun s => lam ^ (a - 4) * (s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2))) (Ioi 0) := by
    intro s hs
    simp only [hg]
    exact kappa_integrand_scale hlam hs
  have hint0 : IntegrableOn
      (fun s : ℝ => lam ^ (a - 4) * (s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2))) (Ioi 0) :=
    (phaseI_integrableOn ha).const_mul (lam ^ (a - 4))
  have hcomp : IntegrableOn (fun s => g (lam ^ 2 * s)) (Ioi 0) :=
    hint0.congr_fun hEq.symm measurableSet_Ioi
  have hint : IntegrableOn g (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff g 0 hl2).1 hcomp
    simpa using this
  refine ⟨hint, ?_⟩
  have h1 := integral_comp_mul_left_Ioi g 0 hl2
  rw [mul_zero] at h1
  have h2 : ∫ s in Ioi (0 : ℝ), g (lam ^ 2 * s) =
      ∫ s in Ioi (0 : ℝ), lam ^ (a - 4) * (s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2)) :=
    setIntegral_congr_fun measurableSet_Ioi hEq
  rw [h2, integral_const_mul, smul_eq_mul] at h1
  have hpow : lam ^ 2 * lam ^ (a - 4) = lam ^ (a - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hlam]
    norm_num
    ring_nf
  have key : ∫ t in Ioi (0 : ℝ), g t = lam ^ 2 * (lam ^ (a - 4) * phaseI a) := by
    unfold phaseI
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hl2.ne', one_mul]
  rw [key, ← mul_assoc, hpow]

/-- `κ^{a-3} = (λ²+t)^{(a-3)/2}` for `κ = (λ²+t)^{1/2}` (the form of the
integrand at main TeX line 2353). -/
theorem kappa_rpow_eq {a lam t : ℝ} (ht : 0 ≤ t) :
    ((lam ^ 2 + t) ^ (1 / 2 : ℝ)) ^ (a - 3) = (lam ^ 2 + t) ^ ((a - 3) / 2) := by
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Norm convergence and the bound of the inverse-root integral (main TeX lines
2338-2359): if `‖J(t)‖ ≤ c t^{-1/2}(λ²+t)^{(a-3)/2}` on `(0,∞)` and `J` is
strongly measurable, then `J` is integrable and
`‖π⁻¹ ∫_0^∞ J‖ ≤ c λ^{a-2} I_a / π`. -/
theorem resolvent_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a lam c : ℝ} (ha : a < 2) (hlam : 0 < lam) (J : ℝ → E)
    (hJm : AEStronglyMeasurable J (volume.restrict (Ioi 0)))
    (hJ : ∀ t ∈ Ioi (0 : ℝ), ‖J t‖ ≤ c * (t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2))) :
    IntegrableOn J (Ioi 0) ∧
      ‖(1 / π) • ∫ t in Ioi (0 : ℝ), J t‖ ≤ c * lam ^ (a - 2) * phaseI a / π := by
  obtain ⟨hint, heq⟩ := kappa_integral ha hlam
  have hbd : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖J t‖ ≤ c * (t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2)) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hJ)
  have hgi := hint.const_mul c
  refine ⟨Integrable.mono' hgi hJm hbd, ?_⟩
  have hn := norm_integral_le_of_norm_le hgi hbd
  rw [integral_const_mul, heq] at hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_eq_mul_inv, one_mul]
  calc π⁻¹ * ‖∫ t in Ioi (0 : ℝ), J t‖ ≤ π⁻¹ * (c * (lam ^ (a - 2) * phaseI a)) := by
        gcongr
    _ = c * lam ^ (a - 2) * phaseI a / π := by ring

/-- `‖Q - 1‖ ≤ 1/6` (main TeX lines 2355-2360 and 2936-2939): if
`Q - 1 = π⁻¹ ∫_0^∞ J(t) dt` with `J` strongly measurable and
`‖J(t)‖ ≤ (c/(1-δ_a)) t^{-1/2}(λ²+t)^{(a-3)/2}`, where
`c λ^{a-2} ≤ δ_a`.  (`c = |z| d` in `L:complex-phase`, `c = D` in
`L:interval-complex`.) -/
theorem q_sub_one_le {E : Type*} [NormedRing E] [NormedSpace ℝ E] {a lam c : ℝ} (ha : a < 2)
    (hlam : 0 < lam) (hcδ : c * lam ^ (a - 2) ≤ deltaA a) (Q : E) (J : ℝ → E)
    (hJm : AEStronglyMeasurable J (volume.restrict (Ioi 0)))
    (hJ : ∀ t ∈ Ioi (0 : ℝ),
      ‖J t‖ ≤ c / (1 - deltaA a) * (t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2)))
    (hQ : Q - 1 = (1 / π) • ∫ t in Ioi (0 : ℝ), J t) :
    ‖Q - 1‖ ≤ 1 / 6 := by
  obtain ⟨_, hn⟩ := resolvent_integral_le ha hlam J hJm hJ
  rw [hQ]
  refine hn.trans (le_of_eq_of_le ?_ (neumann_prefactor_le ha hcδ))
  have h1 := one_sub_deltaA_ge a
  have : (1 - deltaA a) ≠ 0 := by linarith
  field_simp

/-! ## Neumann bounds and the resolvent algebra -/

/-- Neumann series (main TeX lines 2320-2325): in a complete normed ring with
`‖1‖ ≤ 1`, `‖K‖ ≤ δ < 1` gives that `1 - K` is invertible with
`‖(1-K)⁻¹‖ ≤ (1-δ)⁻¹`. -/
theorem neumann_inverse_le {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (h1 : ‖(1 : R)‖ ≤ 1) {K : R} {δ : ℝ} (hK : ‖K‖ ≤ δ) (hδ : δ < 1) :
    IsUnit (1 - K) ∧ ‖Ring.inverse (1 - K)‖ ≤ (1 - δ)⁻¹ := by
  have hlt : ‖K‖ < 1 := lt_of_le_of_lt hK hδ
  refine ⟨⟨Units.oneSub K hlt, Units.val_oneSub K hlt⟩, ?_⟩
  rw [NormedRing.inverse_one_sub K hlt]
  have hg := tsum_geometric_le_of_norm_lt_one K hlt
  have hpos : 0 < 1 - δ := by linarith
  calc ‖((Units.oneSub K hlt)⁻¹ : Rˣ).val‖ = ‖∑' n : ℕ, K ^ n‖ := rfl
    _ ≤ ‖(1 : R)‖ - 1 + (1 - ‖K‖)⁻¹ := hg
    _ ≤ (1 - ‖K‖)⁻¹ := by linarith
    _ ≤ (1 - δ)⁻¹ := inv_anti₀ hpos (by linarith)

/-- The Neumann bounds `7/6` and `6/5` (main TeX lines 2939-2940; "norm at most
two", line 2361): in a complete normed ring with `‖1‖ ≤ 1`, `‖Q - 1‖ ≤ 1/6`
gives `‖Q‖ ≤ 7/6`, `Q` invertible and `‖Q⁻¹‖ ≤ 6/5`. -/
theorem neumann_root_comparison {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (h1 : ‖(1 : R)‖ ≤ 1) {Q : R} (hQ : ‖Q - 1‖ ≤ 1 / 6) :
    ‖Q‖ ≤ 7 / 6 ∧ IsUnit Q ∧ ‖Ring.inverse Q‖ ≤ 6 / 5 := by
  have hQe : Q = 1 - (1 - Q) := by abel
  have hK : ‖1 - Q‖ ≤ 1 / 6 := by rw [norm_sub_rev]; exact hQ
  obtain ⟨hu, hinv⟩ := neumann_inverse_le h1 hK (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · calc ‖Q‖ = ‖1 + (Q - 1)‖ := by congr 1; abel
      _ ≤ ‖(1 : R)‖ + ‖Q - 1‖ := norm_add_le _ _
      _ ≤ 7 / 6 := by linarith
  · rw [hQe]; exact hu
  · rw [hQe]
    calc ‖Ring.inverse (1 - (1 - Q))‖ ≤ (1 - 1 / 6)⁻¹ := hinv
      _ = 6 / 5 := by norm_num

/-- The resolvent difference (main TeX lines 2341-2348 and 2930-2934), as a ring
identity: if `L_λ + t = S U S` and `A_κ = S S` with `S, U` invertible, then
`(SUS)⁻¹ - (SS)⁻¹ = S⁻¹ U⁻¹ (1 - U) S⁻¹`; with `S = A_κ^{1/2}`,
`U = 1 - zK_κ` this is `A_κ^{-1/2}(1-zK_κ)^{-1} zK_κ A_κ^{-1/2}`. -/
theorem resolvent_difference {R : Type*} [Ring R] (S U : Rˣ) :
    ((S * U * S)⁻¹ : Rˣ).val - ((S * S)⁻¹ : Rˣ).val =
      (S⁻¹ : Rˣ).val * (U⁻¹ : Rˣ).val * (1 - U.val) * (S⁻¹ : Rˣ).val := by
  simp only [mul_inv_rev, Units.val_mul]
  rw [mul_sub, mul_one, mul_assoc (S⁻¹ : Rˣ).val (U⁻¹ : Rˣ).val U.val, Units.inv_mul, mul_one,
    sub_mul]
  noncomm_ring

/-- The four-factor bound (main TeX lines 2349-2354): if the factors have norms
at most `1`, `(1-δ)⁻¹`, `c κ^{a-2}` and `κ⁻¹`, their product has norm at most
`(c/(1-δ)) κ^{a-3}`. -/
theorem integrand_factor_le {R : Type*} [NormedRing R] {P U K S : R} {a c δ κ : ℝ}
    (hκ : 0 < κ) (hc : 0 ≤ c) (hδ : δ < 1) (hP : ‖P‖ ≤ 1) (hU : ‖U‖ ≤ (1 - δ)⁻¹)
    (hK : ‖K‖ ≤ c * κ ^ (a - 2)) (hS : ‖S‖ ≤ κ⁻¹) :
    ‖P * U * K * S‖ ≤ c / (1 - δ) * κ ^ (a - 3) := by
  have hpos : 0 < 1 - δ := by linarith
  have hk : κ ^ (a - 2) * κ⁻¹ = κ ^ (a - 3) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hκ]
    congr 1
    ring
  calc ‖P * U * K * S‖ ≤ ‖P‖ * ‖U‖ * ‖K‖ * ‖S‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ 1 * (1 - δ)⁻¹ * (c * κ ^ (a - 2)) * κ⁻¹ := by
        gcongr
    _ = c / (1 - δ) * κ ^ (a - 3) := by
        rw [← hk]
        field_simp

/-! ## The numerical-range parabola (main TeX lines 2373-2396, 2948-2958) -/

/-- Auxiliary (Lean route): `ρ^{a-2} ρ² = ρ^a` for `ρ > 0`. -/
theorem rpow_sub_two_mul_sq {a ρ : ℝ} (hρ : 0 < ρ) : ρ ^ (a - 2) * ρ ^ 2 = ρ ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hρ]
  norm_num

/-- Optimizing the form bound at `ρ = s` (main TeX lines 2374-2376 and 2953-2955):
if `β ≤ d ρ^{a-2}(ρ² + s²)` for every `ρ > 0`, then `β ≤ 2 d s^a`; at `s = 0`
by letting `ρ ↓ 0`. -/
theorem form_opt_le {a d s β : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (hform : ∀ ρ > 0, β ≤ d * ρ ^ (a - 2) * (ρ ^ 2 + s ^ 2)) : β ≤ 2 * d * s ^ a := by
  rcases hs.lt_or_eq with hs | hs
  · have h := hform s hs
    calc β ≤ d * s ^ (a - 2) * (s ^ 2 + s ^ 2) := h
      _ = 2 * d * (s ^ (a - 2) * s ^ 2) := by ring
      _ = 2 * d * s ^ a := by rw [rpow_sub_two_mul_sq hs]
  · subst hs
    rw [Real.zero_rpow ha.ne', mul_zero]
    have hlim : Tendsto (fun ρ : ℝ => d * ρ ^ a) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun ρ : ℝ => d * ρ ^ a) 0 :=
        (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).const_mul d
      have := hc.tendsto
      rw [Real.zero_rpow ha.ne', mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have h := hform ρ hρ
    calc β ≤ d * ρ ^ (a - 2) * (ρ ^ 2 + 0 ^ 2) := h
      _ = d * (ρ ^ (a - 2) * ρ ^ 2) := by ring
      _ = d * ρ ^ a := by rw [rpow_sub_two_mul_sq hρ]

/-- The coupled form bounds of `L:complex-phase` (main TeX lines 2377-2381):
from `|b| ≤ d λ^{a-2}(λ²+s²)`, `|b| ≤ 2 d s^a` and `|z| ≤ δ λ^{2-a}/d`,
`|zb| ≤ δ(s²+λ²)` and `|zb| ≤ 2δλ^{2-a}s^a`. -/
theorem coupled_form_bounds {a d lam s δ : ℝ} {z b : ℂ} (hd : 0 < d) (hlam : 0 < lam)
    (hδ : 0 ≤ δ) (hz : ‖z‖ ≤ δ * lam ^ (2 - a) / d)
    (hb1 : ‖b‖ ≤ d * lam ^ (a - 2) * (lam ^ 2 + s ^ 2)) (hb2 : ‖b‖ ≤ 2 * d * s ^ a) :
    ‖z * b‖ ≤ δ * (s ^ 2 + lam ^ 2) ∧ ‖z * b‖ ≤ 2 * δ * lam ^ (2 - a) * s ^ a := by
  have hl1 : 0 ≤ lam ^ (2 - a) := (Real.rpow_pos_of_pos hlam _).le
  have hq : 0 ≤ δ * lam ^ (2 - a) / d := by positivity
  rw [norm_mul]
  constructor
  · calc ‖z‖ * ‖b‖ ≤ δ * lam ^ (2 - a) / d * (d * lam ^ (a - 2) * (lam ^ 2 + s ^ 2)) := by
          gcongr
      _ = δ * (lam ^ (2 - a) * lam ^ (a - 2)) * (s ^ 2 + lam ^ 2) := by
          field_simp
          ring
      _ = δ * (s ^ 2 + lam ^ 2) := by rw [rpow_two_sub_mul hlam, mul_one]
  · calc ‖z‖ * ‖b‖ ≤ δ * lam ^ (2 - a) / d * (2 * d * s ^ a) := by gcongr
      _ = 2 * δ * lam ^ (2 - a) * s ^ a := by field_simp

/-- The form bounds of `L:interval-complex` (main TeX lines 2948-2956): from
`|v| ≤ D Λ^{a-2}(s²+Λ²)`, `|v| ≤ 2 D s^a` and `D ≤ δ Λ^{2-a}`,
`|v| ≤ δ(s²+Λ²)` and `|v| ≤ 2δΛ^{2-a}s^a`. -/
theorem interval_form_bounds {a D lam s δ : ℝ} {v : ℂ} (hlam : 0 < lam) (hs : 0 ≤ s)
    (hD : D ≤ δ * lam ^ (2 - a))
    (hv1 : ‖v‖ ≤ D * lam ^ (a - 2) * (s ^ 2 + lam ^ 2)) (hv2 : ‖v‖ ≤ 2 * D * s ^ a) :
    ‖v‖ ≤ δ * (s ^ 2 + lam ^ 2) ∧ ‖v‖ ≤ 2 * δ * lam ^ (2 - a) * s ^ a := by
  have hsa : 0 ≤ s ^ a := Real.rpow_nonneg hs _
  constructor
  · calc ‖v‖ ≤ D * lam ^ (a - 2) * (s ^ 2 + lam ^ 2) := hv1
      _ ≤ δ * (s ^ 2 + lam ^ 2) := by
          gcongr
          exact coeff_le_of_le hlam hD
  · calc ‖v‖ ≤ 2 * D * s ^ a := hv2
      _ ≤ 2 * (δ * lam ^ (2 - a)) * s ^ a := by gcongr
      _ = 2 * δ * lam ^ (2 - a) * s ^ a := by ring

/-- `s^{2a} λ^{2-2a} ≤ s² + λ²` (main TeX line 2389), in the form
`(λ^{2-a} s^a)² ≤ λ²(s²+λ²)`, for `0 < a < 1` (weighted AM-GM). -/
theorem young_parabola {a lam s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hs : 0 ≤ s) :
    (lam ^ (2 - a) * s ^ a) ^ 2 ≤ lam ^ 2 * (s ^ 2 + lam ^ 2) := by
  have hl : 0 ≤ lam := hlam.le
  have hag := Real.geom_mean_le_arith_mean2_weighted (w₁ := a) (w₂ := 1 - a) (p₁ := s ^ 2)
    (p₂ := lam ^ 2) ha0.le (by linarith) (sq_nonneg s) (sq_nonneg lam) (by ring)
  have e1 : (s ^ 2) ^ a = (s ^ a) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hs, ← Real.rpow_mul hs]
    ring_nf
  have e2 : (lam ^ (2 - a)) ^ 2 = lam ^ 2 * (lam ^ 2) ^ (1 - a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hl, ← Real.rpow_mul hl,
      ← Real.rpow_add hlam]
    congr 1
    push_cast
    ring
  have hle : a * s ^ 2 + (1 - a) * lam ^ 2 ≤ s ^ 2 + lam ^ 2 := by
    nlinarith [sq_nonneg s, sq_nonneg lam]
  rw [mul_pow, e2]
  rw [e1] at hag
  have hl2 : 0 ≤ lam ^ 2 := sq_nonneg _
  calc lam ^ 2 * (lam ^ 2) ^ (1 - a) * (s ^ a) ^ 2
      = lam ^ 2 * ((s ^ a) ^ 2 * (lam ^ 2) ^ (1 - a)) := by ring
    _ ≤ lam ^ 2 * (a * s ^ 2 + (1 - a) * lam ^ 2) := by gcongr
    _ ≤ lam ^ 2 * (s ^ 2 + lam ^ 2) := by gcongr

/-- The numerical-range parabola (main TeX lines 2384-2394; reused at lines
2955-2958): for `w = s² - c` with `|c| ≤ δ(s²+λ²)` and `|c| ≤ 2δλ^{2-a}s^a`,
`0 ≤ δ ≤ 1/4`, `0 < a < 1`, writing `w = x + iy`:
`x + λ² ≥ (1-δ)(s²+λ²)`, `|y| ≤ 2δλ^{2-a}s^a`,
`y² ≤ (4δ²/(1-δ)) λ²(x+λ²) ≤ λ²(x+λ²)/3` and `x ≥ -λ²/4`. -/
theorem parabola {a lam s δ : ℝ} {c w : ℂ} (ha0 : 0 < a) (ha1 : a < 1) (hlam : 0 < lam)
    (hs : 0 ≤ s) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (hw : w = ((s ^ 2 : ℝ) : ℂ) - c)
    (hc1 : ‖c‖ ≤ δ * (s ^ 2 + lam ^ 2)) (hc2 : ‖c‖ ≤ 2 * δ * lam ^ (2 - a) * s ^ a) :
    (1 - δ) * (s ^ 2 + lam ^ 2) ≤ w.re + lam ^ 2 ∧
      |w.im| ≤ 2 * δ * lam ^ (2 - a) * s ^ a ∧
      w.im ^ 2 ≤ 4 * δ ^ 2 / (1 - δ) * lam ^ 2 * (w.re + lam ^ 2) ∧
      w.im ^ 2 ≤ 1 / 3 * lam ^ 2 * (w.re + lam ^ 2) ∧
      -(lam ^ 2 / 4) ≤ w.re := by
  have hre : w.re = s ^ 2 - c.re := by rw [hw, Complex.sub_re, Complex.ofReal_re]
  have him : w.im = -c.im := by rw [hw, Complex.sub_im, Complex.ofReal_im, zero_sub]
  have hcre := Complex.abs_re_le_norm c
  have hcim := Complex.abs_im_le_norm c
  have hx : (1 - δ) * (s ^ 2 + lam ^ 2) ≤ w.re + lam ^ 2 := by
    rw [hre]
    have := le_abs_self c.re
    nlinarith
  have hy : |w.im| ≤ 2 * δ * lam ^ (2 - a) * s ^ a := by
    rw [him, abs_neg]; exact hcim.trans hc2
  have hpos : 0 < 1 - δ := by linarith
  have hY := young_parabola ha0 ha1 hlam hs
  have hy2 : w.im ^ 2 ≤ 4 * δ ^ 2 * (lam ^ 2 * (s ^ 2 + lam ^ 2)) := by
    have h0 : 0 ≤ 2 * δ * lam ^ (2 - a) * s ^ a := le_trans (abs_nonneg _) hy
    calc w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * δ * lam ^ (2 - a) * s ^ a) ^ 2 := by gcongr
      _ = 4 * δ ^ 2 * (lam ^ (2 - a) * s ^ a) ^ 2 := by ring
      _ ≤ 4 * δ ^ 2 * (lam ^ 2 * (s ^ 2 + lam ^ 2)) := by gcongr
  have hpar : w.im ^ 2 ≤ 4 * δ ^ 2 / (1 - δ) * lam ^ 2 * (w.re + lam ^ 2) := by
    have hs2 : s ^ 2 + lam ^ 2 ≤ (w.re + lam ^ 2) / (1 - δ) := by
      rw [le_div_iff₀ hpos]; linarith
    calc w.im ^ 2 ≤ 4 * δ ^ 2 * (lam ^ 2 * (s ^ 2 + lam ^ 2)) := hy2
      _ ≤ 4 * δ ^ 2 * (lam ^ 2 * ((w.re + lam ^ 2) / (1 - δ))) := by gcongr
      _ = 4 * δ ^ 2 / (1 - δ) * lam ^ 2 * (w.re + lam ^ 2) := by ring
  have hxl : 0 ≤ w.re + lam ^ 2 := by nlinarith [sq_nonneg s, sq_nonneg lam]
  refine ⟨hx, hy, hpar, ?_, ?_⟩
  · calc w.im ^ 2 ≤ 4 * δ ^ 2 / (1 - δ) * lam ^ 2 * (w.re + lam ^ 2) := hpar
      _ ≤ 1 / 3 * lam ^ 2 * (w.re + lam ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (parabola_coeff_le hδ0 hδ) (sq_nonneg _)) hxl
  · nlinarith [sq_nonneg s, sq_nonneg lam]

/-- `|w| ≤ x + 2λ²` on the parabola (main TeX line 2395). -/
theorem norm_le_of_parabola {lam : ℝ} {w : ℂ} (hpar : w.im ^ 2 ≤ 1 / 3 * lam ^ 2 * (w.re + lam ^ 2))
    (hx : -(lam ^ 2 / 4) ≤ w.re) : ‖w‖ ≤ w.re + 2 * lam ^ 2 := by
  have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hX : 0 ≤ w.re + 2 * lam ^ 2 := by nlinarith [sq_nonneg lam]
  have hsq : ‖w‖ ^ 2 ≤ (w.re + 2 * lam ^ 2) ^ 2 := by
    rw [hn]; nlinarith [sq_nonneg lam]
  by_contra hcon
  replace hcon := lt_of_not_ge hcon
  nlinarith [norm_nonneg w]

/-- Every square root `r` of `w` has `|Im r| ≤ λ` when `|w| ≤ Re w + 2λ²`
(main TeX lines 2395-2396). -/
theorem im_root_le {lam : ℝ} (hlam : 0 ≤ lam) {r w : ℂ} (hr : r ^ 2 = w)
    (hw : ‖w‖ ≤ w.re + 2 * lam ^ 2) : |r.im| ≤ lam := by
  have hre : w.re = r.re ^ 2 - r.im ^ 2 := by rw [← hr]; simp [sq]
  have hn : ‖w‖ = r.re ^ 2 + r.im ^ 2 := by
    rw [← hr, norm_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hre, hn] at hw
  have h2 : r.im ^ 2 ≤ lam ^ 2 := by linarith
  by_contra hcon
  replace hcon := lt_of_not_ge hcon
  nlinarith [abs_nonneg r.im, sq_abs r.im]

/-! ## The scalar functions `C_h`, `F_h`, `H_h` (main TeX lines 2398-2429) -/

/-- The principal square root `w^{1/2}` (`cpow` with exponent `1/2`). -/
def csqrt (w : ℂ) : ℂ := w ^ (((2 : ℕ) : ℂ)⁻¹)

/-- Auxiliary (Lean route): `(√w)² = w`. -/
theorem csqrt_sq (w : ℂ) : csqrt w ^ 2 = w :=
  Complex.cpow_nat_inv_pow w (by norm_num)

/-- Auxiliary (Lean route): `|√w|² = |w|`. -/
theorem norm_csqrt_sq (w : ℂ) : ‖csqrt w‖ ^ 2 = ‖w‖ := by
  rw [← norm_pow, csqrt_sq]

/-- Auxiliary (Lean route): `√w ≠ 0` for `w ≠ 0`. -/
theorem csqrt_ne_zero {w : ℂ} (hw : w ≠ 0) : csqrt w ≠ 0 := by
  intro h
  apply hw
  rw [← csqrt_sq w, h]
  ring

/-- `G_h(w) = sin(h√w)/√w` (main TeX line 2444), with its removable value
`G_h(0) = h`.  Since `sin(hr)/r` is even in `r`, the branch of `√w` is
irrelevant. -/
def phaseG (h : ℝ) (w : ℂ) : ℂ :=
  if w = 0 then (h : ℂ) else Complex.sin (h * csqrt w) / csqrt w

/-- `C_h(w) = cos(h√w)` (main TeX line 2400); even in the root. -/
def phaseC (h : ℝ) (w : ℂ) : ℂ := Complex.cos (h * csqrt w)

/-- `F_h(w) = √(w+λ²) sin(h√w)/√w` (main TeX line 2401), with the principal
branch of `√(w+λ²)`. -/
def phaseF (h lam : ℝ) (w : ℂ) : ℂ := csqrt (w + ((lam ^ 2 : ℝ) : ℂ)) * phaseG h w

/-- `H_h(w) = (w/√(w+λ²)) sin(h√w)/√w` (main TeX lines 2402-2403); its value at
`w = 0` is `0`. -/
def phaseH (h lam : ℝ) (w : ℂ) : ℂ := w / csqrt (w + ((lam ^ 2 : ℝ) : ℂ)) * phaseG h w

/-- Auxiliary (Lean route): `|cos r| ≤ e^μ` and `|sin r| ≤ e^μ` when
`|Im r| ≤ μ`. -/
theorem norm_cos_sin_le {r : ℂ} {μ : ℝ} (hr : |r.im| ≤ μ) :
    ‖Complex.cos r‖ ≤ Real.exp μ ∧ ‖Complex.sin r‖ ≤ Real.exp μ := by
  have h1 : ‖Complex.exp (r * Complex.I)‖ ≤ Real.exp μ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have : (r * Complex.I).re = -r.im := by simp
    rw [this]
    exact (neg_le_abs _).trans hr
  have h2 : ‖Complex.exp (-r * Complex.I)‖ ≤ Real.exp μ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have : (-r * Complex.I).re = r.im := by simp
    rw [this]
    exact (le_abs_self _).trans hr
  constructor
  · rw [Complex.cos.eq_1, norm_div]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this, div_le_iff₀ (by norm_num)]
    calc ‖Complex.exp (r * Complex.I) + Complex.exp (-r * Complex.I)‖
        ≤ ‖Complex.exp (r * Complex.I)‖ + ‖Complex.exp (-r * Complex.I)‖ := norm_add_le _ _
      _ ≤ Real.exp μ * 2 := by linarith
  · rw [Complex.sin.eq_1, norm_div, norm_mul, Complex.norm_I, mul_one]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this, div_le_iff₀ (by norm_num)]
    calc ‖Complex.exp (-r * Complex.I) - Complex.exp (r * Complex.I)‖
        ≤ ‖Complex.exp (-r * Complex.I)‖ + ‖Complex.exp (r * Complex.I)‖ := norm_sub_le _ _
      _ ≤ Real.exp μ * 2 := by linarith

/-- Auxiliary (Lean route): `|Im(t r)| ≤ λ h` for `0 ≤ t ≤ h`, `|Im r| ≤ λ`. -/
theorem im_scale_le {r : ℂ} {lam h t : ℝ} (hr : |r.im| ≤ lam) (ht0 : 0 ≤ t) (hth : t ≤ h) :
    |((t : ℂ) * r).im| ≤ lam * h := by
  have hl : 0 ≤ lam := (abs_nonneg _).trans hr
  rw [Complex.im_ofReal_mul, abs_mul, abs_of_nonneg ht0]
  calc t * |r.im| ≤ h * lam := mul_le_mul hth hr (abs_nonneg _) (ht0.trans hth)
    _ = lam * h := by ring

/-- `|sin(h r)| ≤ h |r| e^{λh}` for `|Im r| ≤ λ`, `h ≥ 0`: the bound
`|sin(h√w)/√w| ≤ h e^{λh}` of main TeX lines 2414-2416.  Lean route: the mean
value inequality for `t ↦ sin(tr)` on `[0,h]` instead of the integral identity
`sin(h√w)/√w = ∫_0^h cos(r√w) dr`. -/
theorem norm_sin_le_mul {r : ℂ} {lam h : ℝ} (hr : |r.im| ≤ lam) (hh : 0 ≤ h) :
    ‖Complex.sin (h * r)‖ ≤ h * ‖r‖ * Real.exp (lam * h) := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) h, HasDerivWithinAt (fun t : ℝ => Complex.sin (t * r))
      (Complex.cos (t * r) * r) (Icc 0 h) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℂ => Complex.sin (x * r)) (Complex.cos (t * r) * (1 * r)) t :=
      ((hasDerivAt_id (t : ℂ)).mul_const r).csin
    rw [one_mul] at h1
    exact h1.comp_ofReal.hasDerivWithinAt
  have hbd : ∀ t ∈ Ico (0 : ℝ) h, ‖Complex.cos (t * r) * r‖ ≤ Real.exp (lam * h) * ‖r‖ := by
    intro t ht
    rw [norm_mul]
    gcongr
    exact (norm_cos_sin_le (im_scale_le hr ht.1 ht.2.le)).1
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbd h ⟨hh, le_rfl⟩
  simp only [Complex.ofReal_zero, zero_mul, Complex.sin_zero, sub_zero] at this
  calc ‖Complex.sin (h * r)‖ ≤ Real.exp (lam * h) * ‖r‖ * h := this
    _ = h * ‖r‖ * Real.exp (lam * h) := by ring

/-- `|C_h(w)| ≤ e^{λh}` when `|Im √w| ≤ λ`, `h ≥ 0` (main TeX lines 2409, 2413-2414). -/
theorem norm_phaseC_le {lam h : ℝ} {w : ℂ} (hr : |(csqrt w).im| ≤ lam) (hh : 0 ≤ h) :
    ‖phaseC h w‖ ≤ Real.exp (lam * h) :=
  (norm_cos_sin_le (im_scale_le hr hh le_rfl)).1

/-- `|G_h(w)| ≤ h e^{λh}`, including `w = 0` (main TeX lines 2414-2416). -/
theorem norm_phaseG_le {lam h : ℝ} {w : ℂ} (hr : |(csqrt w).im| ≤ lam) (hh : 0 ≤ h) :
    ‖phaseG h w‖ ≤ h * Real.exp (lam * h) := by
  have hl : 0 ≤ lam := (abs_nonneg _).trans hr
  unfold phaseG
  split_ifs with hw
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
    have : 1 ≤ Real.exp (lam * h) := Real.one_le_exp (by positivity)
    nlinarith
  · have hne := csqrt_ne_zero hw
    have hpos : 0 < ‖csqrt w‖ := norm_pos_iff.2 hne
    rw [norm_div, div_le_iff₀ hpos]
    calc ‖Complex.sin (h * csqrt w)‖ ≤ h * ‖csqrt w‖ * Real.exp (lam * h) :=
          norm_sin_le_mul hr hh
      _ = h * Real.exp (lam * h) * ‖csqrt w‖ := by ring

/-- `|G_h(w)| ≤ e^{λh}/|√w|` for `w ≠ 0` (main TeX lines 2413-2414, 2420). -/
theorem norm_phaseG_le' {lam h : ℝ} {w : ℂ} (hw : w ≠ 0) (hr : |(csqrt w).im| ≤ lam) (hh : 0 ≤ h) :
    ‖phaseG h w‖ ≤ Real.exp (lam * h) / ‖csqrt w‖ := by
  simp only [phaseG, hw, ↓reduceIte]
  rw [norm_div]
  gcongr
  exact (norm_cos_sin_le (im_scale_le hr hh le_rfl)).2

/-- The case `|w| ≤ λ²/2` of the `F_h` bound (main TeX lines 2416-2419):
`|F_h(w)| ≤ √(3/2) λ h e^{λh}`. -/
theorem phaseF_small {lam h : ℝ} {w : ℂ} (hlam : 0 < lam) (hr : |(csqrt w).im| ≤ lam)
    (hh : 0 ≤ h) (hw : ‖w‖ ≤ lam ^ 2 / 2) :
    ‖phaseF h lam w‖ ≤ √(3 / 2) * lam * h * Real.exp (lam * h) := by
  unfold phaseF
  rw [norm_mul]
  have hz : ‖csqrt (w + ((lam ^ 2 : ℝ) : ℂ))‖ ≤ √(3 / 2) * lam := by
    have h1 : ‖csqrt (w + ((lam ^ 2 : ℝ) : ℂ))‖ ^ 2 ≤ 3 / 2 * lam ^ 2 := by
      rw [norm_csqrt_sq]
      calc ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ ≤ ‖w‖ + ‖((lam ^ 2 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ lam ^ 2 / 2 + lam ^ 2 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg lam)]
            linarith
        _ = 3 / 2 * lam ^ 2 := by ring
    have h2 := Real.abs_le_sqrt h1
    rw [abs_of_nonneg (norm_nonneg _), Real.sqrt_mul (by norm_num), Real.sqrt_sq hlam.le] at h2
    exact h2
  calc ‖csqrt (w + ((lam ^ 2 : ℝ) : ℂ))‖ * ‖phaseG h w‖
      ≤ (√(3 / 2) * lam) * (h * Real.exp (lam * h)) :=
        mul_le_mul hz (norm_phaseG_le hr hh) (norm_nonneg _) (by positivity)
    _ = √(3 / 2) * lam * h * Real.exp (lam * h) := by ring

/-- The case `|w| > λ²/2` of the `F_h` bound (main TeX lines 2420-2421):
`|w+λ²|/|w| ≤ 3`, so `|F_h(w)| ≤ √3 e^{λh}`. -/
theorem phaseF_large {lam h : ℝ} {w : ℂ} (hr : |(csqrt w).im| ≤ lam)
    (hh : 0 ≤ h) (hw : lam ^ 2 / 2 < ‖w‖) :
    ‖phaseF h lam w‖ ≤ √3 * Real.exp (lam * h) := by
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    nlinarith [sq_nonneg lam]
  have hne := csqrt_ne_zero hw0
  have hpos : 0 < ‖csqrt w‖ := norm_pos_iff.2 hne
  unfold phaseF
  rw [norm_mul]
  have hratio : ‖csqrt (w + ((lam ^ 2 : ℝ) : ℂ))‖ ≤ √3 * ‖csqrt w‖ := by
    have h1 : ‖csqrt (w + ((lam ^ 2 : ℝ) : ℂ))‖ ^ 2 ≤ 3 * ‖csqrt w‖ ^ 2 := by
      rw [norm_csqrt_sq, norm_csqrt_sq]
      calc ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ ≤ ‖w‖ + ‖((lam ^ 2 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ 3 * ‖w‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg lam)]
            linarith
    have h2 := Real.abs_le_sqrt h1
    rw [abs_of_nonneg (norm_nonneg _), Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (norm_nonneg _)] at h2
    exact h2
  calc ‖csqrt (w + ((lam ^ 2 : ℝ) : ℂ))‖ * ‖phaseG h w‖
      ≤ (√3 * ‖csqrt w‖) * (Real.exp (lam * h) / ‖csqrt w‖) :=
        mul_le_mul hratio (norm_phaseG_le' hw0 hr hh) (norm_nonneg _) (by positivity)
    _ = √3 * Real.exp (lam * h) := by field_simp

/-- `|F_h(w)| ≤ 2(1+λh) e^{λh}` when `|Im √w| ≤ λ` (main TeX lines 2410,
2416-2421). -/
theorem norm_phaseF_le {lam h : ℝ} {w : ℂ} (hlam : 0 < lam) (hr : |(csqrt w).im| ≤ lam)
    (hh : 0 ≤ h) : ‖phaseF h lam w‖ ≤ 2 * (1 + lam * h) * Real.exp (lam * h) := by
  have he : 0 < Real.exp (lam * h) := Real.exp_pos _
  have hlh : 0 ≤ lam * h := mul_nonneg hlam.le hh
  have hs32 : √(3 / 2) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs3 : √3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rcases le_or_gt ‖w‖ (lam ^ 2 / 2) with hw | hw
  · refine (phaseF_small hlam hr hh hw).trans ?_
    have : √(3 / 2) * lam * h ≤ 2 * (1 + lam * h) := by
      have := mul_le_mul_of_nonneg_right hs32 hlh
      nlinarith
    exact mul_le_mul_of_nonneg_right this he.le
  · refine (phaseF_large hr hh hw).trans ?_
    exact mul_le_mul_of_nonneg_right (by nlinarith) he.le

/-- `|w|/|w+λ²| ≤ 1 + λ²/|w+λ²| ≤ 1 + (1-δ)⁻¹ ≤ 7/3` when
`Re(w+λ²) ≥ (1-δ)λ²` and `δ ≤ 1/4` (main TeX lines 2424-2426), in the
multiplied form `|w| ≤ (7/3)|w+λ²|`. -/
theorem range_ratio_le {lam δ : ℝ} {w : ℂ} (hlam : 0 < lam) (hδ : δ ≤ 1 / 4)
    (hre : (1 - δ) * lam ^ 2 ≤ w.re + lam ^ 2) :
    ‖w‖ ≤ (1 + (1 - δ)⁻¹) * ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ ∧
      ‖w‖ ≤ 7 / 3 * ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ := by
  have hpos : 0 < 1 - δ := by linarith
  have hl2 : 0 < lam ^ 2 := by positivity
  have hsum : (w + ((lam ^ 2 : ℝ) : ℂ)).re = w.re + lam ^ 2 := by
    rw [Complex.add_re, Complex.ofReal_re]
  have hN : (1 - δ) * lam ^ 2 ≤ ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ := by
    rw [← hsum] at hre
    exact hre.trans (Complex.re_le_norm _)
  have hNpos : 0 < ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ := lt_of_lt_of_le (by positivity) hN
  have htri : ‖w‖ ≤ ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ + lam ^ 2 := by
    have h := norm_sub_le (w + ((lam ^ 2 : ℝ) : ℂ)) ((lam ^ 2 : ℝ) : ℂ)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg lam)] at h
    exact h
  have hl : lam ^ 2 ≤ (1 - δ)⁻¹ * ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ := by
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  have h1 : ‖w‖ ≤ (1 + (1 - δ)⁻¹) * ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ := by
    rw [add_mul, one_mul]; linarith
  refine ⟨h1, h1.trans ?_⟩
  gcongr
  exact range_ratio_const_le hδ

/-- `|H_h(w)| ≤ 2 e^{λh}` when `|Im √w| ≤ λ`, `Re(w+λ²) ≥ (1-δ)λ²`,
`δ ≤ 1/4` (main TeX lines 2411, 2422-2429), via
`H_h(w) = √w sin(h√w)/√(w+λ²)`. -/
theorem norm_phaseH_le {lam h δ : ℝ} {w : ℂ} (hlam : 0 < lam) (hδ : δ ≤ 1 / 4)
    (hr : |(csqrt w).im| ≤ lam) (hh : 0 ≤ h) (hre : (1 - δ) * lam ^ 2 ≤ w.re + lam ^ 2) :
    ‖phaseH h lam w‖ ≤ 2 * Real.exp (lam * h) := by
  have he : 0 < Real.exp (lam * h) := Real.exp_pos _
  by_cases hw0 : w = 0
  · rw [phaseH, hw0, zero_div, zero_mul, norm_zero]; positivity
  obtain ⟨_, h73⟩ := range_ratio_le hlam hδ hre
  set ζ := csqrt (w + ((lam ^ 2 : ℝ) : ℂ)) with hζ
  have hpos : 0 < 1 - δ := by linarith
  have hsum : (w + ((lam ^ 2 : ℝ) : ℂ)).re = w.re + lam ^ 2 := by
    rw [Complex.add_re, Complex.ofReal_re]
  have hN : 0 < ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ := by
    have : 0 < (w + ((lam ^ 2 : ℝ) : ℂ)).re := by rw [hsum]; nlinarith [sq_pos_of_pos hlam]
    exact lt_of_lt_of_le this (Complex.re_le_norm _)
  have hζ2 : ‖ζ‖ ^ 2 = ‖w + ((lam ^ 2 : ℝ) : ℂ)‖ := norm_csqrt_sq _
  have hζpos : 0 < ‖ζ‖ := by
    rcases (norm_nonneg ζ).lt_or_eq with h | h
    · exact h
    · rw [← h] at hζ2; linarith
  have hrne := csqrt_ne_zero hw0
  have hrpos : 0 < ‖csqrt w‖ := norm_pos_iff.2 hrne
  have hr2 : ‖csqrt w‖ ^ 2 = ‖w‖ := norm_csqrt_sq w
  have hrz : ‖csqrt w‖ ≤ 2 * ‖ζ‖ := by
    have : ‖csqrt w‖ ^ 2 ≤ (2 * ‖ζ‖) ^ 2 := by
      rw [hr2, mul_pow, hζ2]; linarith
    exact (pow_le_pow_iff_left₀ hrpos.le (by positivity) (by norm_num)).1 this
  have hG : phaseG h w = Complex.sin (h * csqrt w) / csqrt w := by
    simp only [phaseG, hw0, ↓reduceIte]
  have hform : phaseH h lam w = csqrt w * Complex.sin (h * csqrt w) / ζ := by
    rw [phaseH, hG, ← hζ]
    set r := csqrt w with hrdef
    have hw' : w = r ^ 2 := (csqrt_sq w).symm
    rw [hw']
    field_simp
  rw [hform, norm_div, norm_mul, div_le_iff₀ hζpos]
  have hs := (norm_cos_sin_le (im_scale_le hr hh le_rfl)).2
  calc ‖csqrt w‖ * ‖Complex.sin (h * csqrt w)‖ ≤ (2 * ‖ζ‖) * Real.exp (lam * h) :=
        mul_le_mul hrz hs (norm_nonneg _) (by positivity)
    _ = 2 * Real.exp (lam * h) * ‖ζ‖ := by ring

/-- The scalar layer of `L:complex-phase` on one point of the numerical range
(main TeX lines 2384-2429; reused for `L:interval-complex` at lines 2955-2959):
for `w = s² - c` with `|c| ≤ δ(s²+λ²)`, `|c| ≤ 2δλ^{2-a}s^a`, `0 ≤ δ ≤ 1/4`,
`0 < a < 1`, `λ > 0`, `h ≥ 0`: `|w| ≤ Re w + 2λ²`, every square root of `w` has
imaginary part at most `λ` in absolute value, and `|C_h(w)| ≤ e^{λh}`,
`|F_h(w)| ≤ 2(1+λh)e^{λh}`, `|H_h(w)| ≤ 2e^{λh}`. -/
theorem phase_scalar_bounds {a lam s δ h : ℝ} {c w : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hlam : 0 < lam) (hs : 0 ≤ s) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (hh : 0 ≤ h)
    (hw : w = ((s ^ 2 : ℝ) : ℂ) - c)
    (hc1 : ‖c‖ ≤ δ * (s ^ 2 + lam ^ 2)) (hc2 : ‖c‖ ≤ 2 * δ * lam ^ (2 - a) * s ^ a) :
    ‖w‖ ≤ w.re + 2 * lam ^ 2 ∧ (∀ r : ℂ, r ^ 2 = w → |r.im| ≤ lam) ∧
      ‖phaseC h w‖ ≤ Real.exp (lam * h) ∧
      ‖phaseF h lam w‖ ≤ 2 * (1 + lam * h) * Real.exp (lam * h) ∧
      ‖phaseH h lam w‖ ≤ 2 * Real.exp (lam * h) := by
  obtain ⟨hx, -, -, hpar, hxl⟩ := parabola ha0 ha1 hlam hs hδ0 hδ hw hc1 hc2
  have hn := norm_le_of_parabola hpar hxl
  have hroot : ∀ r : ℂ, r ^ 2 = w → |r.im| ≤ lam := fun r hr => im_root_le hlam.le hr hn
  have hr := hroot _ (csqrt_sq w)
  have hre : (1 - δ) * lam ^ 2 ≤ w.re + lam ^ 2 := by
    have : (1 - δ) * lam ^ 2 ≤ (1 - δ) * (s ^ 2 + lam ^ 2) := by
      have : 0 ≤ 1 - δ := by linarith
      nlinarith [sq_nonneg s]
    linarith
  exact ⟨hn, hroot, norm_phaseC_le hr hh, norm_phaseF_le hlam hr hh,
    norm_phaseH_le hlam hδ hr hh hre⟩

/-! ## Assembly constants and the block bound (main TeX lines 2430-2460) -/

/-- `1 + √2 ≤ 3`: Crouzeix-Palencia turns the scalar bounds `1, 2(1+λh), 2`
(times `e^{λh}`) into `3, 6(1+λh), 6` (main TeX lines 2430-2431). -/
theorem one_add_sqrt_two_le : 1 + √2 ≤ 3 := by
  have : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- `(39 + 12λh) e^{λh} ≤ 39(1+λh) e^{λh} ≤ 100 e^{2λh}` for `λh ≥ 0` (main TeX
lines 2457-2459). -/
theorem block_constant_le {x : ℝ} (hx : 0 ≤ x) :
    (39 + 12 * x) * Real.exp x ≤ 39 * (1 + x) * Real.exp x ∧
      39 * (1 + x) * Real.exp x ≤ 100 * Real.exp (2 * x) := by
  have he : 0 < Real.exp x := Real.exp_pos x
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  constructor
  · gcongr; linarith
  · have : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
    rw [this]
    nlinarith

/-- A 2×2 block operator on `E ⊕ E` with the ℓ² norm has norm at most the sum of
its four block norms (main TeX lines 2453-2455), stated pointwise. -/
theorem block_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T11 T12 T21 T22 : E →L[ℂ] E) (u v : E) :
    √(‖T11 u + T12 v‖ ^ 2 + ‖T21 u + T22 v‖ ^ 2) ≤
      (‖T11‖ + ‖T12‖ + ‖T21‖ + ‖T22‖) * √(‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  set N := √(‖u‖ ^ 2 + ‖v‖ ^ 2) with hN
  have hu : ‖u‖ ≤ N := by
    have := Real.abs_le_sqrt (x := ‖u‖) (y := ‖u‖ ^ 2 + ‖v‖ ^ 2) (by nlinarith [sq_nonneg ‖v‖])
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hv : ‖v‖ ≤ N := by
    have := Real.abs_le_sqrt (x := ‖v‖) (y := ‖u‖ ^ 2 + ‖v‖ ^ 2) (by nlinarith [sq_nonneg ‖u‖])
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have h1 : ‖T11 u + T12 v‖ ≤ (‖T11‖ + ‖T12‖) * N := by
    calc ‖T11 u + T12 v‖ ≤ ‖T11‖ * ‖u‖ + ‖T12‖ * ‖v‖ :=
          (norm_add_le _ _).trans (add_le_add (T11.le_opNorm u) (T12.le_opNorm v))
      _ ≤ ‖T11‖ * N + ‖T12‖ * N := by gcongr
      _ = _ := by ring
  have h2 : ‖T21 u + T22 v‖ ≤ (‖T21‖ + ‖T22‖) * N := by
    calc ‖T21 u + T22 v‖ ≤ ‖T21‖ * ‖u‖ + ‖T22‖ * ‖v‖ :=
          (norm_add_le _ _).trans (add_le_add (T21.le_opNorm u) (T22.le_opNorm v))
      _ ≤ ‖T21‖ * N + ‖T22‖ * N := by gcongr
      _ = _ := by ring
  have hp : 0 ≤ ‖T11 u + T12 v‖ := norm_nonneg _
  have hq : 0 ≤ ‖T21 u + T22 v‖ := norm_nonneg _
  calc √(‖T11 u + T12 v‖ ^ 2 + ‖T21 u + T22 v‖ ^ 2)
      ≤ √((‖T11 u + T12 v‖ + ‖T21 u + T22 v‖) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = ‖T11 u + T12 v‖ + ‖T21 u + T22 v‖ := Real.sqrt_sq (by positivity)
    _ ≤ (‖T11‖ + ‖T12‖) * N + (‖T21‖ + ‖T22‖) * N := add_le_add h1 h2
    _ = (‖T11‖ + ‖T12‖ + ‖T21‖ + ‖T22‖) * N := by ring

/-- The assembly of main TeX lines 2433-2460 (and 2959-2963): with weighted blocks
`C_h(L)`, `F_h(L) P1`, `-P2 H_h(L)`, `P2 C_h(L) P1`, where `‖P1‖, ‖P2‖ ≤ 2` and
`‖C_h(L)‖ ≤ 3e^{λh}`, `‖F_h(L)‖ ≤ 6(1+λh)e^{λh}`, `‖H_h(L)‖ ≤ 6e^{λh}`, the block
norms are at most `3, 12(1+λh), 12, 12` times `e^{λh}`, and the block map has
ℓ²-operator bound `(39+12λh)e^{λh} ≤ 100 e^{2λh}`. -/
theorem complex_phase_assembly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 ≤ h) (Cop Fop Hop P1 P2 : E →L[ℂ] E)
    (hP1 : ‖P1‖ ≤ 2) (hP2 : ‖P2‖ ≤ 2) (hC : ‖Cop‖ ≤ 3 * Real.exp (lam * h))
    (hF : ‖Fop‖ ≤ 6 * (1 + lam * h) * Real.exp (lam * h)) (hH : ‖Hop‖ ≤ 6 * Real.exp (lam * h))
    (u v : E) :
    √(‖Cop u + (Fop ∘L P1) v‖ ^ 2 + ‖(-(P2 ∘L Hop)) u + (P2 ∘L Cop ∘L P1) v‖ ^ 2) ≤
      100 * Real.exp (2 * (lam * h)) * √(‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have he : 0 < Real.exp (lam * h) := Real.exp_pos _
  have hlh : 0 ≤ lam * h := mul_nonneg hlam hh
  have b2 : ‖Fop ∘L P1‖ ≤ 12 * (1 + lam * h) * Real.exp (lam * h) := by
    calc ‖Fop ∘L P1‖ ≤ ‖Fop‖ * ‖P1‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 6 * (1 + lam * h) * Real.exp (lam * h) * 2 :=
          mul_le_mul hF hP1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have b3 : ‖-(P2 ∘L Hop)‖ ≤ 12 * Real.exp (lam * h) := by
    rw [norm_neg]
    calc ‖P2 ∘L Hop‖ ≤ ‖P2‖ * ‖Hop‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * (6 * Real.exp (lam * h)) := mul_le_mul hP2 hH (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have b4 : ‖P2 ∘L Cop ∘L P1‖ ≤ 12 * Real.exp (lam * h) := by
    calc ‖P2 ∘L Cop ∘L P1‖ ≤ ‖P2‖ * (‖Cop‖ * ‖P1‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 2 * (3 * Real.exp (lam * h) * 2) := by
          gcongr
      _ = _ := by ring
  have hsum : ‖Cop‖ + ‖Fop ∘L P1‖ + ‖-(P2 ∘L Hop)‖ + ‖P2 ∘L Cop ∘L P1‖ ≤
      100 * Real.exp (2 * (lam * h)) := by
    obtain ⟨k1, k2⟩ := block_constant_le hlh
    nlinarith
  calc _ ≤ (‖Cop‖ + ‖Fop ∘L P1‖ + ‖-(P2 ∘L Hop)‖ + ‖P2 ∘L Cop ∘L P1‖) *
        √(‖u‖ ^ 2 + ‖v‖ ^ 2) := block_norm_le _ _ _ _ u v
    _ ≤ _ := by gcongr

/-! ## The interval metric: the `L:interval-complex` instance (main TeX lines 2966-2981) -/

/-- The phase-weight change in multiplier form (main TeX lines 2966-2970): for a
spectral value `x ≥ 0` of `A_0`, `(ρ_new² + x)⁻¹ ≤ max{1, ρ_old/ρ_new}² (ρ_old² + x)⁻¹`;
this is the multiplier inequality behind
`‖z‖_{ρ_new} ≤ max{1, ρ_old/ρ_new} ‖z‖_{ρ_old}`. -/
theorem phase_weight_change {ρo ρn x : ℝ} (ho : 0 < ρo) (hn : 0 < ρn) (hx : 0 ≤ x) :
    (ρn ^ 2 + x)⁻¹ ≤ (max 1 (ρo / ρn)) ^ 2 * (ρo ^ 2 + x)⁻¹ := by
  have hA : 0 < ρn ^ 2 + x := by positivity
  have hB : 0 < ρo ^ 2 + x := by positivity
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hA hB, one_mul]
  rcases le_or_gt ρo ρn with h | h
  · have : max 1 (ρo / ρn) = 1 := max_eq_left ((div_le_one hn).2 h)
    rw [this]
    nlinarith
  · have hm : max 1 (ρo / ρn) = ρo / ρn := max_eq_right ((one_le_div hn).2 h.le)
    rw [hm, div_pow]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hsq : ρn ^ 2 ≤ ρo ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hx]

/-- Auxiliary (Lean route): `1 + Σ_E x_i ≤ ∏_E (1 + x_i)` for `x_i ≥ 0`. -/
theorem one_add_sum_le_prod {ι : Type*} (E : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ E, 0 ≤ x i) :
    1 + ∑ i ∈ E, x i ≤ ∏ i ∈ E, (1 + x i) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | insert j E hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hxj := hx j (Finset.mem_insert_self j E)
    have hS : 0 ≤ ∑ i ∈ E, x i := Finset.sum_nonneg (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    nlinarith

/-- Auxiliary (Lean route): `1 ≤ ∏_E (1 + x_i)` for `x_i ≥ 0`. -/
theorem one_le_prod_one_add {ι : Type*} (E : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ E, 0 ≤ x i) :
    1 ≤ ∏ i ∈ E, (1 + x i) := by
  have := one_add_sum_le_prod E x hx
  have hS : 0 ≤ ∑ i ∈ E, x i := Finset.sum_nonneg hx
  linarith

/-- The jump ratio (main TeX lines 2971-2978): with `E` the ending, `S` the
starting and `R` the remaining fields at a jump, and weights `ω_i ≥ 0`,
`max{1, (λ+Σ_R ω+Σ_E ω)/(λ+Σ_R ω+Σ_S ω)} ≤ 1 + Σ_E ω_i/λ ≤ ∏_E (1+ω_i/λ)`. -/
theorem jump_ratio_le {ι : Type*} {lam : ℝ} (hlam : 0 < lam) (ω : ι → ℝ) (R E S : Finset ι)
    (hω : ∀ i, 0 ≤ ω i) :
    max 1 ((lam + ∑ i ∈ R, ω i + ∑ i ∈ E, ω i) / (lam + ∑ i ∈ R, ω i + ∑ i ∈ S, ω i)) ≤
        1 + (∑ i ∈ E, ω i) / lam ∧
      1 + (∑ i ∈ E, ω i) / lam ≤ ∏ i ∈ E, (1 + ω i / lam) := by
  have hR : 0 ≤ ∑ i ∈ R, ω i := Finset.sum_nonneg (fun i _ => hω i)
  have hE : 0 ≤ ∑ i ∈ E, ω i := Finset.sum_nonneg (fun i _ => hω i)
  have hS : 0 ≤ ∑ i ∈ S, ω i := Finset.sum_nonneg (fun i _ => hω i)
  have hden : 0 < lam + ∑ i ∈ R, ω i + ∑ i ∈ S, ω i := by linarith
  have hEl : 0 ≤ (∑ i ∈ E, ω i) / lam := div_nonneg hE hlam.le
  constructor
  · refine max_le (by linarith) ?_
    rw [div_le_iff₀ hden]
    have : (∑ i ∈ E, ω i) / lam * (lam + ∑ i ∈ R, ω i + ∑ i ∈ S, ω i) ≥ ∑ i ∈ E, ω i := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hlam]
      nlinarith
    nlinarith
  · rw [Finset.sum_div]
    exact one_add_sum_le_prod E (fun i => ω i / lam) (fun i _ => div_nonneg (hω i) hlam.le)

/-- The `L:interval-complex` instance of `E:interval-metric` (main TeX lines
2914-2916, 2979-2981): over finitely many jumps `j ∈ J` whose ending sets `E_j`
are pairwise disjoint and contained in the set `I` of fields present (each
connected interval ends once; a final return to `X_λ` counts as an ending jump),
the product of the per-jump losses
`max{1, (λ+Σ_{R_j}ω+Σ_{E_j}ω)/(λ+Σ_{R_j}ω+Σ_{S_j}ω)}` is at most
`∏_{i∈I}(1+ω_i/λ)`.  The jump data `R_j, E_j, S_j` are taken as given finite
sets; the time partition and the composition of the phase norms with the
segment propagators (the general telescoping lemma, wave L10-FS0) are not
modelled. -/
theorem interval_metric_instance {ι κ : Type*} [DecidableEq ι] {lam : ℝ} (hlam : 0 < lam)
    (ω : ι → ℝ) (hω : ∀ i, 0 ≤ ω i) (I : Finset ι) (J : Finset κ) (R E S : κ → Finset ι)
    (hdisj : (J : Set κ).PairwiseDisjoint E) (hsub : ∀ j ∈ J, E j ⊆ I) :
    ∏ j ∈ J, max 1 ((lam + ∑ i ∈ R j, ω i + ∑ i ∈ E j, ω i) /
        (lam + ∑ i ∈ R j, ω i + ∑ i ∈ S j, ω i)) ≤ ∏ i ∈ I, (1 + ω i / lam) := by
  have hx : ∀ i, 0 ≤ ω i / lam := fun i => div_nonneg (hω i) hlam.le
  calc ∏ j ∈ J, max 1 ((lam + ∑ i ∈ R j, ω i + ∑ i ∈ E j, ω i) /
        (lam + ∑ i ∈ R j, ω i + ∑ i ∈ S j, ω i))
      ≤ ∏ j ∈ J, ∏ i ∈ E j, (1 + ω i / lam) := by
        apply Finset.prod_le_prod₀
        · intro j _; exact le_trans zero_le_one (le_max_left _ _)
        · intro j _
          obtain ⟨h1, h2⟩ := jump_ratio_le hlam ω (R j) (E j) (S j) hω
          exact h1.trans h2
    _ = ∏ i ∈ J.biUnion E, (1 + ω i / lam) := (Finset.prod_biUnion hdisj).symm
    _ ≤ ∏ i ∈ I, (1 + ω i / lam) := by
        have hsub' : J.biUnion E ⊆ I := Finset.biUnion_subset.2 hsub
        rw [← Finset.prod_sdiff hsub']
        have h1 := one_le_prod_one_add (I \ J.biUnion E) (fun i => ω i / lam) (fun i _ => hx i)
        have h2 := one_le_prod_one_add (J.biUnion E) (fun i => ω i / lam) (fun i _ => hx i)
        nlinarith

/-! ## The phase-range conclusion -/

/-- The conclusion of the numerical-range and scalar steps at one point `w`
(main TeX lines 2384-2429): the two inequalities for some `s ≥ 0`, the parabola,
`x ≥ -λ²/4`, `|w| ≤ x + 2λ²`, `|Im r| ≤ λ` for every square root `r` of `w`, and
the three scalar bounds. -/
def PhaseRangeBounds (a δ lam h : ℝ) (w : ℂ) : Prop :=
  (∃ s : ℝ, 0 ≤ s ∧ (1 - δ) * (s ^ 2 + lam ^ 2) ≤ w.re + lam ^ 2 ∧
      |w.im| ≤ 2 * δ * lam ^ (2 - a) * s ^ a) ∧
    w.im ^ 2 ≤ 1 / 3 * lam ^ 2 * (w.re + lam ^ 2) ∧ -(lam ^ 2 / 4) ≤ w.re ∧
    ‖w‖ ≤ w.re + 2 * lam ^ 2 ∧ (∀ r : ℂ, r ^ 2 = w → |r.im| ≤ lam) ∧
    ‖phaseC h w‖ ≤ Real.exp (lam * h) ∧
    ‖phaseF h lam w‖ ≤ 2 * (1 + lam * h) * Real.exp (lam * h) ∧
    ‖phaseH h lam w‖ ≤ 2 * Real.exp (lam * h)

/-- `PhaseRangeBounds` at `w = s² - c` from the two bounds on `c` (main TeX lines
2384-2429): `parabola` and `phase_scalar_bounds` combined. -/
theorem phaseRangeBounds_of {a lam s δ h : ℝ} {c w : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hlam : 0 < lam) (hs : 0 ≤ s) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (hh : 0 ≤ h)
    (hw : w = ((s ^ 2 : ℝ) : ℂ) - c)
    (hc1 : ‖c‖ ≤ δ * (s ^ 2 + lam ^ 2)) (hc2 : ‖c‖ ≤ 2 * δ * lam ^ (2 - a) * s ^ a) :
    PhaseRangeBounds a δ lam h w := by
  obtain ⟨hx, hy, -, hpar, hxl⟩ := parabola ha0 ha1 hlam hs hδ0 hδ hw hc1 hc2
  obtain ⟨hn, hroot, hC, hF, hH⟩ := phase_scalar_bounds ha0 ha1 hlam hs hδ0 hδ hh hw hc1 hc2
  exact ⟨⟨s, hs, hx, hy⟩, hpar, hxl, hn, hroot, hC, hF, hH⟩

/-! ## The operator layer: numerical range and the sandwich form bound -/

section Operators

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The numerical range `W(T) = {⟨Tu,u⟩ : ‖u‖ = 1}` (main TeX line 2283).
Mathlib's inner product is conjugate-linear in the FIRST slot, so the TeX's
`⟨Tu,u⟩` is `⟪u, T u⟫`. -/
def numRange (T : H →L[ℂ] H) : Set ℂ := {w | ∃ u : H, ‖u‖ = 1 ∧ w = inner ℂ u (T u)}

/-- `A_ρ = ρ² + A_0` (main TeX line 2290). -/
def shiftOp (A0 : H →L[ℂ] H) (ρ : ℝ) : H →L[ℂ] H := A0 + algebraMap ℝ (H →L[ℂ] H) (ρ ^ 2)

/-- `A_ρ^{-1/2}`: the inverse of the continuous-functional-calculus square root
of `A_ρ`.  For `A_0 ≥ 0` and `ρ > 0` the square root is proved invertible
(`sqrtShift_isUnit`), so `Ring.inverse` is the genuine inverse. -/
def invSqrtShift (A0 : H →L[ℂ] H) (ρ : ℝ) : H →L[ℂ] H := Ring.inverse (CFC.sqrt (shiftOp A0 ρ))

/-- Auxiliary (Lean route): `A_ρ ≥ 0` for `A_0 ≥ 0`. -/
theorem shiftOp_nonneg {A0 : H →L[ℂ] H} (hA : A0.IsPositive) (ρ : ℝ) : 0 ≤ shiftOp A0 ρ :=
  add_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA)
    (algebraMap_nonneg _ (sq_nonneg ρ))

/-- Auxiliary (Lean route): `A_ρ` is invertible for `A_0 ≥ 0`, `ρ > 0` (its
spectrum lies in `[ρ², ∞)`). -/
theorem shiftOp_isUnit {A0 : H →L[ℂ] H} (hA : A0.IsPositive) {ρ : ℝ} (hρ : 0 < ρ) :
    IsUnit (shiftOp A0 ρ) := by
  have h0 : (0 : H →L[ℂ] H) ≤ A0 := ContinuousLinearMap.nonneg_iff_isPositive.mpr hA
  have hnot : (-(ρ ^ 2)) ∉ spectrum ℝ A0 := by
    intro hm
    have := spectrum_nonneg_of_nonneg h0 hm
    nlinarith [sq_pos_of_pos hρ]
  have hu := spectrum.notMem_iff.mp hnot
  have : shiftOp A0 ρ = -((algebraMap ℝ (H →L[ℂ] H)) (-(ρ ^ 2)) - A0) := by
    simp [shiftOp, map_neg]
  rw [this]
  exact hu.neg

/-- Auxiliary (Lean route): `A_ρ^{1/2}` is invertible for `A_0 ≥ 0`, `ρ > 0`. -/
theorem sqrtShift_isUnit {A0 : H →L[ℂ] H} (hA : A0.IsPositive) {ρ : ℝ} (hρ : 0 < ρ) :
    IsUnit (CFC.sqrt (shiftOp A0 ρ)) := by
  have hm : CFC.sqrt (shiftOp A0 ρ) * CFC.sqrt (shiftOp A0 ρ) = shiftOp A0 ρ :=
    CFC.sqrt_mul_sqrt_self _ (shiftOp_nonneg hA ρ)
  have hu := shiftOp_isUnit hA hρ
  rw [← hm] at hu
  exact ((Commute.refl _).isUnit_mul_iff.mp hu).1

/-- Auxiliary (Lean route): `A_ρ^{-1/2} A_ρ^{1/2} = 1`. -/
theorem invSqrtShift_mul_sqrt {A0 : H →L[ℂ] H} (hA : A0.IsPositive) {ρ : ℝ} (hρ : 0 < ρ) :
    invSqrtShift A0 ρ * CFC.sqrt (shiftOp A0 ρ) = 1 :=
  Ring.inverse_mul_cancel _ (sqrtShift_isUnit hA hρ)

/-- Auxiliary (Lean route): `A_ρ^{1/2} A_ρ^{-1/2} = 1`. -/
theorem sqrt_mul_invSqrtShift {A0 : H →L[ℂ] H} (hA : A0.IsPositive) {ρ : ℝ} (hρ : 0 < ρ) :
    CFC.sqrt (shiftOp A0 ρ) * invSqrtShift A0 ρ = 1 :=
  Ring.mul_inverse_cancel _ (sqrtShift_isUnit hA hρ)

/-- Auxiliary (Lean route): `A_ρ^{-1/2}` is selfadjoint. -/
theorem invSqrtShift_selfAdjoint {A0 : H →L[ℂ] H} (hA : A0.IsPositive) {ρ : ℝ} (hρ : 0 < ρ) :
    IsSelfAdjoint (invSqrtShift A0 ρ) := by
  have hS : IsSelfAdjoint (CFC.sqrt (shiftOp A0 ρ)) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have h1 : star (invSqrtShift A0 ρ) * CFC.sqrt (shiftOp A0 ρ) = 1 := by
    rw [← hS.star_eq, ← star_mul, sqrt_mul_invSqrtShift hA hρ, star_one]
  show star (invSqrtShift A0 ρ) = invSqrtShift A0 ρ
  calc star (invSqrtShift A0 ρ)
      = star (invSqrtShift A0 ρ) * (CFC.sqrt (shiftOp A0 ρ) * invSqrtShift A0 ρ) := by
        rw [sqrt_mul_invSqrtShift hA hρ, mul_one]
    _ = invSqrtShift A0 ρ := by rw [← mul_assoc, h1, one_mul]

/-- The form consequence of `E:abstract-sandwich` (used at main TeX lines
2374-2381 and 2948-2954 without comment): if
`‖A_ρ^{-1/2} B A_ρ^{-1/2}‖ ≤ c`, then `|⟨Bu,u⟩| ≤ c (ρ²‖u‖² + ⟨A_0u,u⟩)`, i.e.
`c ⟨A_ρ u, u⟩`.  `B` is an arbitrary bounded operator. -/
theorem form_of_sandwich {A0 B : H →L[ℂ] H} (hA0 : A0.IsPositive) {ρ c : ℝ} (hρ : 0 < ρ)
    (hK : ‖invSqrtShift A0 ρ * B * invSqrtShift A0 ρ‖ ≤ c) (u : H) :
    ‖inner ℂ u (B u)‖ ≤ c * (ρ ^ 2 * ‖u‖ ^ 2 + (inner ℂ u (A0 u)).re) := by
  set S := CFC.sqrt (shiftOp A0 ρ) with hSdef
  set R := invSqrtShift A0 ρ with hRdef
  have hRS : R * S = 1 := invSqrtShift_mul_sqrt hA0 hρ
  have hRsa : IsSelfAdjoint R := invSqrtShift_selfAdjoint hA0 hρ
  have hSsa : IsSelfAdjoint S := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hSS : S * S = shiftOp A0 ρ := CFC.sqrt_mul_sqrt_self _ (shiftOp_nonneg hA0 ρ)
  have hRSu : R (S u) = u := by
    change (R * S) u = u
    rw [hRS]
    rfl
  have hid : inner ℂ u (B u) = inner ℂ (S u) ((R * B * R) (S u)) := by
    change inner ℂ u (B u) = inner ℂ (S u) (R (B (R (S u))))
    rw [hRSu, ← ContinuousLinearMap.adjoint_inner_left R (B u) (S u),
      ← ContinuousLinearMap.star_eq_adjoint, hRsa.star_eq, hRSu]
  have hSSu : S (S u) = A0 u + (ρ ^ 2) • u := by
    change (S * S) u = _
    rw [hSS]
    simp [shiftOp, Algebra.algebraMap_eq_smul_one]
  have huu : (inner ℂ u u).re = ‖u‖ ^ 2 := @inner_self_eq_norm_sq ℂ _ _ _ _ u
  have hnorm : ‖S u‖ ^ 2 = ρ ^ 2 * ‖u‖ ^ 2 + (inner ℂ u (A0 u)).re := by
    have h1 : ‖S u‖ ^ 2 = (inner ℂ (S u) (S u)).re := (@inner_self_eq_norm_sq ℂ _ _ _ _ (S u)).symm
    rw [h1, ← ContinuousLinearMap.adjoint_inner_right S u (S u),
      ← ContinuousLinearMap.star_eq_adjoint, hSsa.star_eq, hSSu, inner_add_right,
      ← Complex.coe_smul, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul, huu]
    ring
  have hc : 0 ≤ c := le_trans (norm_nonneg _) hK
  calc ‖inner ℂ u (B u)‖ = ‖inner ℂ (S u) ((R * B * R) (S u))‖ := by rw [hid]
    _ ≤ ‖S u‖ * ‖(R * B * R) (S u)‖ := norm_inner_le_norm _ _
    _ ≤ ‖S u‖ * (‖R * B * R‖ * ‖S u‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖S u‖ * (c * ‖S u‖) := by gcongr
    _ = c * ‖S u‖ ^ 2 := by ring
    _ = c * (ρ ^ 2 * ‖u‖ ^ 2 + (inner ℂ u (A0 u)).re) := by rw [hnorm]

/-- The adjoint has the identical sandwich norm (main TeX lines 2920-2924):
`‖A_ρ^{-1/2} V^* A_ρ^{-1/2}‖ = ‖A_ρ^{-1/2} V A_ρ^{-1/2}‖`. -/
theorem sandwich_adjoint_norm {A0 : H →L[ℂ] H} (hA0 : A0.IsPositive) {ρ : ℝ} (hρ : 0 < ρ)
    (V : H →L[ℂ] H) :
    ‖invSqrtShift A0 ρ * ContinuousLinearMap.adjoint V * invSqrtShift A0 ρ‖ =
      ‖invSqrtShift A0 ρ * V * invSqrtShift A0 ρ‖ := by
  have hRsa := invSqrtShift_selfAdjoint hA0 hρ
  rw [← ContinuousLinearMap.star_eq_adjoint,
    ← norm_star (invSqrtShift A0 ρ * V * invSqrtShift A0 ρ),
    star_mul, star_mul, hRsa.star_eq, mul_assoc]

omit [CompleteSpace H] in
/-- A point of the numerical range of `A_0 - T`: for a unit vector `u`,
`⟨(A_0 - T)u, u⟩ = s² - ⟨Tu,u⟩` with `s = √⟨A_0u,u⟩` and `⟨A_0u,u⟩ ≥ 0` real. -/
theorem numRange_sub_point {A0 : H →L[ℂ] H} (hA0 : A0.IsPositive) (T : H →L[ℂ] H) (u : H) :
    0 ≤ (inner ℂ u (A0 u)).re ∧
      inner ℂ u ((A0 - T) u) = (((√(inner ℂ u (A0 u)).re) ^ 2 : ℝ) : ℂ) - inner ℂ u (T u) := by
  have h0 : (0 : ℂ) ≤ inner ℂ u (A0 u) := hA0.inner_nonneg_right u
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 h0
  refine ⟨hre, ?_⟩
  change inner ℂ u (A0 u - T u) = _
  rw [inner_sub_right, Real.sq_sqrt hre]
  congr 1
  exact Complex.ext (by simp) (by simp [him])

/-- `L:complex-phase`, numerical-range and scalar layer, with the manuscript's
hypotheses (main TeX lines 2288-2301, proof 2373-2429): `A_0` bounded,
nonnegative and selfadjoint (`IsPositive`), `B` bounded selfadjoint,
`0 < a < 1`, `d > 0`, `E:abstract-sandwich` with `A_ρ^{-1/2}` the inverse CFC
square root, `λ > 0`, `|z| ≤ δ_a λ^{2-a}/d`, `h ≥ 0`.  Conclusion: every point
of `W(L)`, `L = A_0 - zB`, satisfies `PhaseRangeBounds a δ_a λ h`.  Narrower
than the lemma: the propagator bound `E:complex-phase-bound` is in
`complex_phase_paper` under supplied inputs.  `hB` (selfadjointness) is carried
but not used: the scalar route allows complex `⟨Bu,u⟩`. -/
theorem complex_phase_range_paper (A0 B : H →L[ℂ] H) (hA0 : A0.IsPositive)
    (_hB : IsSelfAdjoint B) {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd : 0 < d)
    (hsand : ∀ ρ > 0, ‖invSqrtShift A0 ρ * B * invSqrtShift A0 ρ‖ ≤ d * ρ ^ (a - 2))
    {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : ‖z‖ ≤ deltaA a * lam ^ (2 - a) / d)
    {h : ℝ} (hh : 0 ≤ h) :
    ∀ w ∈ numRange (A0 - z • B), PhaseRangeBounds a (deltaA a) lam h w := by
  rintro w ⟨u, hu, rfl⟩
  have hδ0 : 0 ≤ deltaA a := (deltaA_pos (by linarith)).le
  obtain ⟨hre, hpt⟩ := numRange_sub_point hA0 (z • B) u
  set s := √(inner ℂ u (A0 u)).re with hsdef
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (inner ℂ u (A0 u)).re := Real.sq_sqrt hre
  set b := inner ℂ u (B u) with hbdef
  have hform : ∀ ρ > 0, ‖b‖ ≤ d * ρ ^ (a - 2) * (ρ ^ 2 + s ^ 2) := by
    intro ρ hρ
    have := form_of_sandwich hA0 hρ (hsand ρ hρ) u
    rw [hu, ← hs2, one_pow, mul_one] at this
    exact this
  have hb2 := form_opt_le ha0 hs hform
  have hb1 : ‖b‖ ≤ d * lam ^ (a - 2) * (lam ^ 2 + s ^ 2) := hform lam hlam
  obtain ⟨hc1, hc2⟩ := coupled_form_bounds hd hlam hδ0 hz hb1 hb2
  have hw : inner ℂ u ((A0 - z • B) u) = ((s ^ 2 : ℝ) : ℂ) - z * b := by
    rw [hpt]
    change ((s ^ 2 : ℝ) : ℂ) - inner ℂ u (z • B u) = _
    rw [inner_smul_right]
  exact phaseRangeBounds_of ha0 ha1 hlam hs hδ0 (deltaA_le_quarter a) hh hw hc1 hc2

/-- `L:interval-complex`, numerical-range and scalar layer, with the
manuscript's hypotheses (main TeX lines 2899-2908, proof 2919-2924 and
2948-2959): `A_0` bounded nonnegative selfadjoint, `V` bounded (not necessarily
selfadjoint), `‖A_ρ^{-1/2}VA_ρ^{-1/2}‖ ≤ Dρ^{a-2}`, `0 < a < 1`,
`D ≤ δ_a Λ^{2-a}`, `Λ > 0`, `h ≥ 0`.  Conclusions: the adjoint `V^*` has the
same sandwich bound, and every point of `W(A_0 - V)` satisfies
`PhaseRangeBounds a δ_a Λ h`. -/
theorem interval_complex_range_paper (A0 V : H →L[ℂ] H) (hA0 : A0.IsPositive) {a D : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hsand : ∀ ρ > 0, ‖invSqrtShift A0 ρ * V * invSqrtShift A0 ρ‖ ≤ D * ρ ^ (a - 2))
    {Λ : ℝ} (hΛ : 0 < Λ) (hD : D ≤ deltaA a * Λ ^ (2 - a)) {h : ℝ} (hh : 0 ≤ h) :
    (∀ ρ > 0, ‖invSqrtShift A0 ρ * ContinuousLinearMap.adjoint V * invSqrtShift A0 ρ‖ ≤
        D * ρ ^ (a - 2)) ∧
      ∀ w ∈ numRange (A0 - V), PhaseRangeBounds a (deltaA a) Λ h w := by
  refine ⟨fun ρ hρ => by rw [sandwich_adjoint_norm hA0 hρ]; exact hsand ρ hρ, ?_⟩
  rintro w ⟨u, hu, rfl⟩
  have hδ0 : 0 ≤ deltaA a := (deltaA_pos (by linarith)).le
  obtain ⟨hre, hpt⟩ := numRange_sub_point hA0 V u
  set s := √(inner ℂ u (A0 u)).re with hsdef
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (inner ℂ u (A0 u)).re := Real.sq_sqrt hre
  set v := inner ℂ u (V u) with hvdef
  have hform : ∀ ρ > 0, ‖v‖ ≤ D * ρ ^ (a - 2) * (ρ ^ 2 + s ^ 2) := by
    intro ρ hρ
    have := form_of_sandwich hA0 hρ (hsand ρ hρ) u
    rw [hu, ← hs2, one_pow, mul_one] at this
    exact this
  have hv2 := form_opt_le ha0 hs hform
  have hv1 : ‖v‖ ≤ D * Λ ^ (a - 2) * (s ^ 2 + Λ ^ 2) := by
    rw [add_comm (s ^ 2)]; exact hform Λ hΛ
  obtain ⟨hc1, hc2⟩ := interval_form_bounds hΛ hs hD hv1 hv2
  exact phaseRangeBounds_of ha0 ha1 hΛ hs hδ0 (deltaA_le_quarter a) hh hpt hc1 hc2

omit [CompleteSpace H] in
/-- Auxiliary (Lean route): `‖1‖ ≤ 1` in `H →L[ℂ] H`. -/
theorem norm_one_clm_le : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le

/-- Auxiliary (Lean route): the common supplied-input deduction of the two
propagator wrappers.  From the phase-range bounds on `W(L)`, Crouzeix-Palencia
for `C_h, F_h, H_h` (supplied), and the inverse-root representation of `Q'`
(supplied), conclude `‖Q'^*‖ ≤ 7/6`, `‖(Q'^{-1})^*‖ ≤ 6/5` and the bound
`100 e^{2λh}` for the weighted block map. -/
theorem phase_block_of_inputs {a lam h c : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hlam : 0 < lam)
    (hh : 0 ≤ h) (hcδ : c * lam ^ (a - 2) ≤ deltaA a) (L : H →L[ℂ] H)
    (hrange : ∀ w ∈ numRange L, PhaseRangeBounds a (deltaA a) lam h w)
    (Cop Fop Hop : H →L[ℂ] H)
    (hCPC : ∀ M ≥ 0, (∀ w ∈ numRange L, ‖phaseC h w‖ ≤ M) → ‖Cop‖ ≤ (1 + √2) * M)
    (hCPF : ∀ M ≥ 0, (∀ w ∈ numRange L, ‖phaseF h lam w‖ ≤ M) → ‖Fop‖ ≤ (1 + √2) * M)
    (hCPH : ∀ M ≥ 0, (∀ w ∈ numRange L, ‖phaseH h lam w‖ ≤ M) → ‖Hop‖ ≤ (1 + √2) * M)
    (Q' : H →L[ℂ] H) (J : ℝ → H →L[ℂ] H) (hJm : AEStronglyMeasurable J (volume.restrict (Ioi 0)))
    (hJ : ∀ t ∈ Ioi (0 : ℝ),
      ‖J t‖ ≤ c / (1 - deltaA a) * (t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2)))
    (hQ' : Q' - 1 = (1 / π) • ∫ t in Ioi (0 : ℝ), J t) :
    ‖Cop‖ ≤ 3 * Real.exp (lam * h) ∧ ‖Fop‖ ≤ 6 * (1 + lam * h) * Real.exp (lam * h) ∧
      ‖Hop‖ ≤ 6 * Real.exp (lam * h) ∧ ‖Q' - 1‖ ≤ 1 / 6 ∧ IsUnit Q' ∧
      ‖ContinuousLinearMap.adjoint Q'‖ ≤ 7 / 6 ∧
      ‖ContinuousLinearMap.adjoint (Ring.inverse Q')‖ ≤ 6 / 5 ∧
      ∀ u v : H,
        √(‖Cop u + (Fop ∘L ContinuousLinearMap.adjoint Q') v‖ ^ 2 +
            ‖(-(ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Hop)) u +
              (ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Cop ∘L
                ContinuousLinearMap.adjoint Q') v‖ ^ 2) ≤
          100 * Real.exp (2 * (lam * h)) * √(‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have he : 0 < Real.exp (lam * h) := Real.exp_pos _
  have hlh : 0 ≤ lam * h := mul_nonneg hlam.le hh
  have hs2 := one_add_sqrt_two_le
  have hs0 : 0 ≤ 1 + √2 := by positivity
  have hC : ‖Cop‖ ≤ 3 * Real.exp (lam * h) := by
    refine (hCPC _ he.le (fun w hw => (hrange w hw).2.2.2.2.2.1)).trans ?_
    exact mul_le_mul_of_nonneg_right hs2 he.le
  have hF : ‖Fop‖ ≤ 6 * (1 + lam * h) * Real.exp (lam * h) := by
    refine (hCPF _ (by positivity) (fun w hw => (hrange w hw).2.2.2.2.2.2.1)).trans ?_
    have : 0 ≤ 2 * (1 + lam * h) * Real.exp (lam * h) := by positivity
    nlinarith
  have hH : ‖Hop‖ ≤ 6 * Real.exp (lam * h) := by
    refine (hCPH _ (by positivity) (fun w hw => (hrange w hw).2.2.2.2.2.2.2)).trans ?_
    nlinarith
  have hQ1 : ‖Q' - 1‖ ≤ 1 / 6 := q_sub_one_le (by linarith) hlam hcδ Q' J hJm hJ hQ'
  obtain ⟨_, hQu, hQinv⟩ := neumann_root_comparison norm_one_clm_le hQ1
  have hQn : ‖Q'‖ ≤ 7 / 6 := (neumann_root_comparison norm_one_clm_le hQ1).1
  have hP1 : ‖ContinuousLinearMap.adjoint Q'‖ ≤ 7 / 6 := by
    rw [LinearIsometryEquiv.norm_map]; exact hQn
  have hP2 : ‖ContinuousLinearMap.adjoint (Ring.inverse Q')‖ ≤ 6 / 5 := by
    rw [LinearIsometryEquiv.norm_map]; exact hQinv
  refine ⟨hC, hF, hH, hQ1, hQu, hP1, hP2, fun u v => ?_⟩
  exact complex_phase_assembly hlam.le hh Cop Fop Hop _ _ (by linarith) (by linarith) hC hF hH u v

/-- `L:complex-phase` (main TeX lines 2288-2310, proof 2312-2465), propagator
layer, with the manuscript's hypotheses and the SUPPLIED inputs named in the
module doc: Crouzeix-Palencia for `C_h, F_h, H_h` at `L = A_0 - zB` (`hCPC`,
`hCPF`, `hCPH`; `E:cp-input`, lines 2277-2286, 2430-2431) and the inverse-root
integral representation of `Q' = A_λ^{1/2}(L^*_λ)^{-1/2}` with its integrand
bound (`Q'`, `J`, `hJm`, `hJ`, `hQ'`; lines 2329-2354, 2361-2362).
Conclusions: the phase-range bounds on `W(L)`; `‖C_h(L)‖ ≤ 3e^{λh}`,
`‖F_h(L)‖ ≤ 6(1+λh)e^{λh}`, `‖H_h(L)‖ ≤ 6e^{λh}`; `‖Q' - 1‖ ≤ 1/6`,
`‖Q'^*‖ ≤ 7/6`, `‖(Q'^{-1})^*‖ ≤ 6/5`; and the bound `100e^{2λh}` for the
weighted block map of lines 2433-2444 built from these operators.  Narrower:
the identification of that block map with `M_z(h)` (lines 2433-2444,
2461-2464) is not formalized. `_hB` is carried but unused. -/
theorem complex_phase_paper (A0 B : H →L[ℂ] H) (hA0 : A0.IsPositive) (_hB : IsSelfAdjoint B)
    {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd : 0 < d)
    (hsand : ∀ ρ > 0, ‖invSqrtShift A0 ρ * B * invSqrtShift A0 ρ‖ ≤ d * ρ ^ (a - 2))
    {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : ‖z‖ ≤ deltaA a * lam ^ (2 - a) / d)
    {h : ℝ} (hh : 0 ≤ h) (Cop Fop Hop : H →L[ℂ] H)
    (hCPC : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - z • B), ‖phaseC h w‖ ≤ M) → ‖Cop‖ ≤ (1 + √2) * M)
    (hCPF : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - z • B), ‖phaseF h lam w‖ ≤ M) →
      ‖Fop‖ ≤ (1 + √2) * M)
    (hCPH : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - z • B), ‖phaseH h lam w‖ ≤ M) →
      ‖Hop‖ ≤ (1 + √2) * M)
    (Q' : H →L[ℂ] H) (J : ℝ → H →L[ℂ] H) (hJm : AEStronglyMeasurable J (volume.restrict (Ioi 0)))
    (hJ : ∀ t ∈ Ioi (0 : ℝ),
      ‖J t‖ ≤ ‖z‖ * d / (1 - deltaA a) * (t ^ (-(1 / 2 : ℝ)) * (lam ^ 2 + t) ^ ((a - 3) / 2)))
    (hQ' : Q' - 1 = (1 / π) • ∫ t in Ioi (0 : ℝ), J t) :
    (∀ w ∈ numRange (A0 - z • B), PhaseRangeBounds a (deltaA a) lam h w) ∧
      ‖Cop‖ ≤ 3 * Real.exp (lam * h) ∧ ‖Fop‖ ≤ 6 * (1 + lam * h) * Real.exp (lam * h) ∧
      ‖Hop‖ ≤ 6 * Real.exp (lam * h) ∧ ‖Q' - 1‖ ≤ 1 / 6 ∧ IsUnit Q' ∧
      ‖ContinuousLinearMap.adjoint Q'‖ ≤ 7 / 6 ∧
      ‖ContinuousLinearMap.adjoint (Ring.inverse Q')‖ ≤ 6 / 5 ∧
      ∀ u v : H,
        √(‖Cop u + (Fop ∘L ContinuousLinearMap.adjoint Q') v‖ ^ 2 +
            ‖(-(ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Hop)) u +
              (ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Cop ∘L
                ContinuousLinearMap.adjoint Q') v‖ ^ 2) ≤
          100 * Real.exp (2 * (lam * h)) * √(‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hrange := complex_phase_range_paper A0 B hA0 _hB ha0 ha1 hd hsand hlam hz hh
  have hcδ : ‖z‖ * d * lam ^ (a - 2) ≤ deltaA a := by
    refine coeff_le_of_le hlam ?_
    rw [le_div_iff₀ hd] at hz
    exact hz
  exact ⟨hrange, phase_block_of_inputs ha0 ha1 hlam hh hcδ _ hrange Cop Fop Hop hCPC hCPF hCPH
    Q' J hJm hJ hQ'⟩

/-- `L:interval-complex` (main TeX lines 2899-2917, proof 2919-2964), propagator
layer, with the manuscript's hypotheses and the same SUPPLIED inputs as
`complex_phase_paper` for `L = A_0 - V` at weight `Λ` (Crouzeix-Palencia for
the three functions on `W(L)`; the inverse-root representation of
`Q' = A_Λ^{1/2}(L^*_Λ)^{-1/2}` with integrand constant `D/(1-δ_a)`, lines
2929-2937, 2941-2944).  Conclusions: the adjoint sandwich bound, the phase-range
bounds on `W(L)`, the three operator bounds, `‖Q' - 1‖ ≤ 1/6`, the Neumann bounds
`‖Q'^*‖ ≤ 7/6` and `‖(Q'^{-1})^*‖ ≤ 6/5` (lines 2939-2944), and the bound
`100e^{2Λh}` for the weighted block map (lines 2959-2963).  Narrower: the block
map is not identified with the propagator in `X_Λ`; `E:interval-metric` is
`interval_metric_paper`. -/
theorem interval_complex_paper (A0 V : H →L[ℂ] H) (hA0 : A0.IsPositive) {a D : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hsand : ∀ ρ > 0, ‖invSqrtShift A0 ρ * V * invSqrtShift A0 ρ‖ ≤ D * ρ ^ (a - 2))
    {Λ : ℝ} (hΛ : 0 < Λ) (hD : D ≤ deltaA a * Λ ^ (2 - a)) {h : ℝ} (hh : 0 ≤ h)
    (Cop Fop Hop : H →L[ℂ] H)
    (hCPC : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - V), ‖phaseC h w‖ ≤ M) → ‖Cop‖ ≤ (1 + √2) * M)
    (hCPF : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - V), ‖phaseF h Λ w‖ ≤ M) → ‖Fop‖ ≤ (1 + √2) * M)
    (hCPH : ∀ M ≥ 0, (∀ w ∈ numRange (A0 - V), ‖phaseH h Λ w‖ ≤ M) → ‖Hop‖ ≤ (1 + √2) * M)
    (Q' : H →L[ℂ] H) (J : ℝ → H →L[ℂ] H) (hJm : AEStronglyMeasurable J (volume.restrict (Ioi 0)))
    (hJ : ∀ t ∈ Ioi (0 : ℝ),
      ‖J t‖ ≤ D / (1 - deltaA a) * (t ^ (-(1 / 2 : ℝ)) * (Λ ^ 2 + t) ^ ((a - 3) / 2)))
    (hQ' : Q' - 1 = (1 / π) • ∫ t in Ioi (0 : ℝ), J t) :
    (∀ ρ > 0, ‖invSqrtShift A0 ρ * ContinuousLinearMap.adjoint V * invSqrtShift A0 ρ‖ ≤
        D * ρ ^ (a - 2)) ∧
      (∀ w ∈ numRange (A0 - V), PhaseRangeBounds a (deltaA a) Λ h w) ∧
      ‖Cop‖ ≤ 3 * Real.exp (Λ * h) ∧ ‖Fop‖ ≤ 6 * (1 + Λ * h) * Real.exp (Λ * h) ∧
      ‖Hop‖ ≤ 6 * Real.exp (Λ * h) ∧ ‖Q' - 1‖ ≤ 1 / 6 ∧ IsUnit Q' ∧
      ‖ContinuousLinearMap.adjoint Q'‖ ≤ 7 / 6 ∧
      ‖ContinuousLinearMap.adjoint (Ring.inverse Q')‖ ≤ 6 / 5 ∧
      ∀ u v : H,
        √(‖Cop u + (Fop ∘L ContinuousLinearMap.adjoint Q') v‖ ^ 2 +
            ‖(-(ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Hop)) u +
              (ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Cop ∘L
                ContinuousLinearMap.adjoint Q') v‖ ^ 2) ≤
          100 * Real.exp (2 * (Λ * h)) * √(‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  obtain ⟨hadj, hrange⟩ := interval_complex_range_paper A0 V hA0 ha0 ha1 hsand hΛ hD hh
  exact ⟨hadj, hrange, phase_block_of_inputs ha0 ha1 hΛ hh (coeff_le_of_le hΛ hD) _ hrange
    Cop Fop Hop hCPC hCPF hCPH Q' J hJm hJ hQ'⟩

end Operators

/-- `E:interval-metric` in the `L:interval-complex` instance, with the
manuscript's hypotheses (main TeX lines 2909-2916, proof 2966-2981): `λ > 0` and
a positive weight `ω_i` for each field present.  The jump data (remaining,
ending and starting sets) are given as subsets of the field set; each field
ends at exactly one jump, so the ending sets are pairwise disjoint (a final
return to `X_λ` counts as an ending jump).  Positivity of the weights is used
only as nonnegativity.  Conclusion: the
total loss `∏_j max{1, ρ_old/ρ_new}` is at most `∏_i (1+ω_i/λ)`.  The
composition of the phase norms along the time partition (the general telescoping
lemma) is not modelled; see `interval_metric_instance`. -/
theorem interval_metric_paper {ι κ : Type*} [DecidableEq ι] {lam : ℝ} (hlam : 0 < lam)
    (ω : ι → ℝ) (I : Finset ι) (hω : ∀ i ∈ I, 0 < ω i) (J : Finset κ) (R E S : κ → Finset ι)
    (hRI : ∀ j ∈ J, R j ⊆ I) (hSI : ∀ j ∈ J, S j ⊆ I)
    (hdisj : (J : Set κ).PairwiseDisjoint E) (hsub : ∀ j ∈ J, E j ⊆ I) :
    ∏ j ∈ J, max 1 ((lam + ∑ i ∈ R j, ω i + ∑ i ∈ E j, ω i) /
        (lam + ∑ i ∈ R j, ω i + ∑ i ∈ S j, ω i)) ≤ ∏ i ∈ I, (1 + ω i / lam) := by
  classical
  set ω' : ι → ℝ := fun i => if i ∈ I then ω i else 0 with hω'
  have hω'0 : ∀ i, 0 ≤ ω' i := by
    intro i; simp only [hω']; split_ifs with hi
    · exact (hω i hi).le
    · exact le_rfl
  have heq : ∀ T : Finset ι, T ⊆ I → ∑ i ∈ T, ω' i = ∑ i ∈ T, ω i := by
    intro T hT
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp [hω', hT hi]
  have hmain := interval_metric_instance hlam ω' hω'0 I J R E S hdisj hsub
  have hlhs : ∀ j ∈ J,
      max 1 ((lam + ∑ i ∈ R j, ω i + ∑ i ∈ E j, ω i) / (lam + ∑ i ∈ R j, ω i + ∑ i ∈ S j, ω i)) =
      max 1 ((lam + ∑ i ∈ R j, ω' i + ∑ i ∈ E j, ω' i) /
        (lam + ∑ i ∈ R j, ω' i + ∑ i ∈ S j, ω' i)) := by
    intro j hj
    rw [heq _ (hRI j hj), heq _ (hsub j hj), heq _ (hSI j hj)]
  have hrhs : ∏ i ∈ I, (1 + ω' i / lam) = ∏ i ∈ I, (1 + ω i / lam) :=
    Finset.prod_congr rfl (fun i hi => by simp [hω', hi])
  rw [Finset.prod_congr rfl hlhs, ← hrhs]
  exact hmain

end StratonovichHAMSecondMoment.ComplexPhaseScalar
