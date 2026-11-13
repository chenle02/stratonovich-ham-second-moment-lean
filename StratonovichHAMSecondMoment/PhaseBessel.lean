module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:phase-bessel` (Hilbert-valued finite Bessel inequality), display
`E:phase-bessel`, of `notes/integrated_wave_variance.tex`, lines 346-366 at
revision a284420 (statement 346-355, proof 357-366). The lemma cites no labels.
The section's standing assumptions (H:homog, `a = α₀`, the range of `γ`, lines
5-8) are not used by this lemma and are not carried.

Formalized (same assumptions, and more general):
* `phase_bessel`: for any measure space `(X, μ)`, any complete complex inner
  product space `H`, any finite index types `ι` (the family index `k`) and `J`
  (the vector index `j`; the TeX has `J = Fin 2`), an orthonormal family
  `u : ι → J → X → ℂ` in `L²(X; ℂ^J)` and `g : J → X → H` with every `g j` in
  `L²`, the integrands `η ↦ ∑ j, u k j η • g j η` and `η ↦ ∑ j, ‖g j η‖²` are
  integrable (the TeX's "the Bochner integrals exist") and
  `∑ k, ‖∫ ∑ j, u k j • g j‖² ≤ ∫ ∑ j, ‖g j‖²`.
* `phase_bessel_conj`: the same with `conj (u k j)` in place of `u k j`.
* `phase_bessel_paper`: the TeX's statement with its own hypotheses
  (`X = ℝ^d` with Lebesgue measure, `J = Fin 2`, `ι = Fin K`, `H` separable),
  both versions.

Encoding of the hypotheses. `L²(ℝ^d; ℂ²)` is encoded componentwise: each
`u k j` is `MemLp 2`, and orthonormality is the integral identity
`∫ ∑ j, u k j η * conj (u l j η) dη = δ_{kl}` (`IsOrthonormalL2`), which is the
`L²(ℂ^J)` inner product `⟨u_k, u_l⟩` linear in the first slot. Likewise
`g ∈ L²(ℝ^d; H²)` is `MemLp (g j) 2` for each `j`. Measurability and the
existence of the Bochner integrals, implicit in the TeX, are part of `MemLp`
and of the conclusion respectively.
Junk values: the orthonormality integral cannot be a junk `0`, since
`u k j * conj (u l j)` is integrable for `L²` components (`integrable_mul_of_memLp`);
the integrals in the conclusion are of integrable functions, as the conclusion
states.

Convention ledger. Mathlib's inner product `inner ℂ x y` is conjugate-linear in
the FIRST slot; the TeX's (`⟨u_k,u_l⟩ = ∫ ∑ u_{k,j} \overline{u_{l,j}}`) is
linear in the first slot. Orthonormality is stated directly as the integral
identity above, so no Mathlib inner product on `L²` is involved in the
hypothesis, and the inequality itself (a statement about norms) does not depend
on the convention.

Proof route (differs from the TeX). The TeX expands `g` in a countable
orthonormal basis of `H`, applies scalar Bessel coefficientwise and sums with
Parseval and Tonelli; separability of `H` is used only for that basis. Here the
projection argument that the TeX uses for scalar Bessel is run directly in `H`:
with `x k = ∫ ∑ j, u k j • g j` and `φ j η = ∑ k, conj (u k j η) • x k`,
`0 ≤ ∫ ∑ j, ‖g j - φ j‖² = ∫ ∑ j, ‖g j‖² - 2 S + S`, `S = ∑ k, ‖x k‖²`.
No basis, Parseval or separability is needed, so the wrapper carries the TeX's
separability hypothesis unused. No σ-finiteness of `μ` is needed either.
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ComplexConjugate

namespace StratonovichHAMSecondMoment.PhaseBessel

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

/-- Orthonormality of a finite family `u : ι → J → X → ℂ` in `L²(X; ℂ^J)`:
every component is in `L²`, and `∫ ∑ j, u k j η * conj (u l j η) dμ = δ_{kl}`
(inner product linear in the first slot, as in the TeX). -/
def IsOrthonormalL2 (μ : Measure X) (u : ι → J → X → ℂ) : Prop :=
  (∀ k j, MemLp (u k j) 2 μ) ∧
    ∀ k l, ∫ η, ∑ j, u k j η * conj (u l j η) ∂μ = if k = l then 1 else 0

/-- The `k`-th coefficient vector `∫ ∑ j, u k j η • g j η dμ ∈ H` (the vector
inside the norm on the left of `E:phase-bessel`). -/
def coeff (μ : Measure X) (u : ι → J → X → ℂ) (g : J → X → H) (k : ι) : H :=
  ∫ η, ∑ j, u k j η • g j η ∂μ

/-- Auxiliary (proof route): the componentwise conjugate of an `L²` scalar
function is in `L²`. -/
theorem memLp_conj {f : X → ℂ} (hf : MemLp f 2 μ) :
    MemLp (fun η => conj (f η)) 2 μ :=
  hf.star

/-- Auxiliary (proof route): the product of two `L²` scalar functions is
integrable. -/
theorem integrable_mul_of_memLp {f h : X → ℂ} (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) :
    Integrable (fun η => f η * h η) μ :=
  hf.integrable_mul hh

omit [CompleteSpace H] in
/-- Auxiliary (proof route): a scalar `L²` function times an `H`-valued `L²`
function is Bochner integrable. -/
theorem integrable_smul_of_memLp {f : X → ℂ} {h : X → H} (hf : MemLp f 2 μ)
    (hh : MemLp h 2 μ) : Integrable (fun η => f η • h η) μ := by
  have : MemLp (f • h) 1 μ := hf.smul hh
  exact memLp_one_iff_integrable.mp this

omit [CompleteSpace H] [Fintype ι] [DecidableEq ι] in
/-- Auxiliary (proof route): the coefficient integrands are Bochner
integrable. -/
theorem integrable_coeff_integrand {u : ι → J → X → ℂ} {g : J → X → H}
    (hu : ∀ k j, MemLp (u k j) 2 μ) (hg : ∀ j, MemLp (g j) 2 μ) (k : ι) :
    Integrable (fun η => ∑ j, u k j η • g j η) μ :=
  integrable_finsetSum _ fun j _ => integrable_smul_of_memLp (hu k j) (hg j)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Auxiliary (proof route): `η ↦ ∑ j, ‖g j η‖²` is integrable. -/
theorem integrable_sum_norm_sq {g : J → X → H} (hg : ∀ j, MemLp (g j) 2 μ) :
    Integrable (fun η => ∑ j, ‖g j η‖ ^ 2) μ :=
  integrable_finsetSum _ fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hg j).aestronglyMeasurable).mp (hg j)

omit [CompleteSpace H] [DecidableEq ι] in
/-- Auxiliary (proof route): the pointwise expansion of the projection
residual. With `φ j = ∑ k, conj (u k j η) • x k`,
`∑ j, ‖g j - φ j‖² = ∑ j, ‖g j‖² - 2 re A + re B`, where
`A = ∑ k, ⟪x k, ∑ j, u k j • g j⟫` and
`B = ∑ k, ∑ l, (∑ j, u k j * conj (u l j)) * ⟪x k, x l⟫`. -/
theorem residual_expand (a : ι → J → ℂ) (y : J → H) (x : ι → H) :
    ∑ j, ‖y j - ∑ k, conj (a k j) • x k‖ ^ 2 =
      ∑ j, ‖y j‖ ^ 2 - 2 * RCLike.re (∑ k, inner ℂ (x k) (∑ j, a k j • y j)) +
        RCLike.re (∑ k, ∑ l, (∑ j, a k j * conj (a l j)) * inner ℂ (x k) (x l)) := by
  have hA : ∀ j, inner ℂ (∑ k, conj (a k j) • x k) (y j) =
      ∑ k, inner ℂ (x k) (a k j • y j) := by
    intro j
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_conj]
  have hB : ∀ j, inner ℂ (∑ k, conj (a k j) • x k) (∑ l, conj (a l j) • x l) =
      ∑ k, ∑ l, a k j * conj (a l j) * inner ℂ (x k) (x l) := by
    intro j
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_conj]
    ring
  have hpt : ∀ j, ‖y j - ∑ k, conj (a k j) • x k‖ ^ 2 =
      ‖y j‖ ^ 2 - 2 * RCLike.re (∑ k, inner ℂ (x k) (a k j • y j)) +
        RCLike.re (∑ k, ∑ l, a k j * conj (a l j) * inner ℂ (x k) (x l)) := by
    intro j
    rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ), ← hA j, ← hB j,
      inner_self_eq_norm_sq (𝕜 := ℂ)]
    ring
  have hAsum : ∑ k, inner ℂ (x k) (∑ j, a k j • y j) =
      ∑ j, ∑ k, inner ℂ (x k) (a k j • y j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => inner_sum _ _ _
  have hBsum : ∑ k, ∑ l, (∑ j, a k j * conj (a l j)) * inner ℂ (x k) (x l) =
      ∑ j, ∑ k, ∑ l, a k j * conj (a l j) * inner ℂ (x k) (x l) := by
    calc _ = ∑ k, ∑ l, ∑ j, a k j * conj (a l j) * inner ℂ (x k) (x l) := by
          simp_rw [Finset.sum_mul]
      _ = ∑ k, ∑ j, ∑ l, a k j * conj (a l j) * inner ℂ (x k) (x l) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [Finset.sum_congr rfl fun j _ => hpt j, hAsum, hBsum, map_sum, map_sum,
    Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Hilbert-valued finite Bessel inequality (`L:phase-bessel`, display
`E:phase-bessel`), general form: any measure space `(X, μ)`, any complete
complex inner product space `H` (separability not needed), finite index types
`ι` and `J`. Hypotheses: `u` is orthonormal in `L²(X; ℂ^J)` in the sense of
`IsOrthonormalL2`, and every `g j` is in `L²(X; H)`. Conclusion: the coefficient
integrands and `∑ j, ‖g j‖²` are integrable, and
`∑ k, ‖∫ ∑ j, u k j • g j‖² ≤ ∫ ∑ j, ‖g j‖²`. -/
theorem phase_bessel {u : ι → J → X → ℂ} {g : J → X → H}
    (hu : IsOrthonormalL2 μ u) (hg : ∀ j, MemLp (g j) 2 μ) :
    (∀ k, Integrable (fun η => ∑ j, u k j η • g j η) μ) ∧
      Integrable (fun η => ∑ j, ‖g j η‖ ^ 2) μ ∧
      ∑ k, ‖coeff μ u g k‖ ^ 2 ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 ∂μ := by
  obtain ⟨huL, hon⟩ := hu
  have hint := integrable_coeff_integrand huL hg
  have hG := integrable_sum_norm_sq (μ := μ) hg
  refine ⟨hint, hG, ?_⟩
  set x : ι → H := coeff μ u g with hx
  -- the two complex integrands of the expansion
  set A : X → ℂ := fun η => ∑ k, inner ℂ (x k) (∑ j, u k j η • g j η) with hAdef
  set B : X → ℂ := fun η =>
    ∑ k, ∑ l, (∑ j, u k j η * conj (u l j η)) * inner ℂ (x k) (x l) with hBdef
  have hAint : Integrable A μ :=
    integrable_finsetSum _ fun k _ => (hint k).const_inner (x k)
  have hprod : ∀ k l, Integrable (fun η => ∑ j, u k j η * conj (u l j η)) μ :=
    fun k l => integrable_finsetSum _ fun j _ =>
      integrable_mul_of_memLp (huL k j) (memLp_conj (huL l j))
  have hBint : Integrable B μ :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hprod k l).mul_const _
  have hAval : ∫ η, A η ∂μ = ∑ k, inner ℂ (x k) (x k) := by
    simp only [hAdef]
    rw [integral_finsetSum _ fun k _ => (hint k).const_inner (x k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_inner (hint k)]
    rfl
  have hBval : ∫ η, B η ∂μ = ∑ k, inner ℂ (x k) (x k) := by
    simp only [hBdef]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hprod k l).mul_const _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (hprod k l).mul_const _]
    simp_rw [integral_mul_const, hon]
    simp
  -- pointwise expansion of the residual
  have hexp : ∀ η, ∑ j, ‖g j η - ∑ k, conj (u k j η) • x k‖ ^ 2 =
      ∑ j, ‖g j η‖ ^ 2 - 2 * RCLike.re (A η) + RCLike.re (B η) :=
    fun η => residual_expand (fun k j => u k j η) (fun j => g j η) x
  have hnonneg : 0 ≤ ∫ η, ∑ j, ‖g j η - ∑ k, conj (u k j η) • x k‖ ^ 2 ∂μ :=
    integral_nonneg fun η => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_add (f := fun η => ∑ j, ‖g j η‖ ^ 2 - 2 * RCLike.re (A η))
      (hG.sub (hAint.re.const_mul 2)) hBint.re,
    integral_sub (f := fun η => ∑ j, ‖g j η‖ ^ 2) hG (hAint.re.const_mul 2), integral_const_mul,
    integral_re hAint, integral_re hBint, hAval, hBval] at hnonneg
  have hS : RCLike.re (∑ k, inner ℂ (x k) (x k)) = ∑ k, ‖x k‖ ^ 2 := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => inner_self_eq_norm_sq (𝕜 := ℂ) (x k)
  rw [hS] at hnonneg
  linarith

omit [Fintype ι] in
/-- Auxiliary (proof route): the componentwise conjugate of an orthonormal
family is orthonormal (`∫ ∑ conj u_k u_l = conj δ_{kl} = δ_{kl}`). -/
theorem isOrthonormalL2_conj {u : ι → J → X → ℂ} (hu : IsOrthonormalL2 μ u) :
    IsOrthonormalL2 μ (fun k j η => conj (u k j η)) := by
  refine ⟨fun k j => memLp_conj (hu.1 k j), fun k l => ?_⟩
  have h := congrArg conj (hu.2 k l)
  rw [← integral_conj] at h
  simp only [map_sum, map_mul, Complex.conj_conj] at h
  simp only [Complex.conj_conj]
  rw [h]
  split_ifs <;> simp

/-- `L:phase-bessel`, conjugated version ("the same bound holds with
`\overline{u_{k,j}}` in place of `u_{k,j}`"), general form, with the same
hypotheses as `phase_bessel`: integrability of the conjugated coefficient
integrands and of `∑ j, ‖g j‖²`, and
`∑ k, ‖∫ ∑ j, conj (u k j) • g j‖² ≤ ∫ ∑ j, ‖g j‖²`. -/
theorem phase_bessel_conj {u : ι → J → X → ℂ} {g : J → X → H}
    (hu : IsOrthonormalL2 μ u) (hg : ∀ j, MemLp (g j) 2 μ) :
    (∀ k, Integrable (fun η => ∑ j, conj (u k j η) • g j η) μ) ∧
      Integrable (fun η => ∑ j, ‖g j η‖ ^ 2) μ ∧
      ∑ k, ‖∫ η, ∑ j, conj (u k j η) • g j η ∂μ‖ ^ 2 ≤
        ∫ η, ∑ j, ‖g j η‖ ^ 2 ∂μ :=
  phase_bessel (isOrthonormalL2_conj hu) hg

/-- `L:phase-bessel` with the manuscript's own hypotheses
(`notes/integrated_wave_variance.tex` 346-355 at a284420): `H` a separable
complex Hilbert space, `{u_k}_{k < K}` a finite orthonormal family in
`L²(ℝ^d; ℂ²)` (encoded by `IsOrthonormalL2` on `Rd d = EuclideanSpace ℝ (Fin d)`
with Lebesgue measure `volume`), and `g = (g₁, g₂) ∈ L²(ℝ^d; H²)`. Conclusion:
the Bochner integrals exist (integrability of every integrand) and both
`E:phase-bessel` and its conjugated version hold. The separability hypothesis
`_hsep` is carried for fidelity and unused: the proof needs no basis of `H`. -/
theorem phase_bessel_paper {d K : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (_hsep : TopologicalSpace.SeparableSpace H)
    {u : Fin K → Fin 2 → EuclideanSpace ℝ (Fin d) → ℂ}
    {g : Fin 2 → EuclideanSpace ℝ (Fin d) → H}
    (hu : IsOrthonormalL2 volume u) (hg : ∀ j, MemLp (g j) 2 volume) :
    (∀ k, Integrable (fun η => ∑ j, u k j η • g j η)) ∧
      (∀ k, Integrable (fun η => ∑ j, conj (u k j η) • g j η)) ∧
      Integrable (fun η => ∑ j, ‖g j η‖ ^ 2) ∧
      ∑ k, ‖∫ η, ∑ j, u k j η • g j η‖ ^ 2 ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 ∧
      ∑ k, ‖∫ η, ∑ j, conj (u k j η) • g j η‖ ^ 2 ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := phase_bessel hu hg
  obtain ⟨h4, -, h5⟩ := phase_bessel_conj hu hg
  exact ⟨h1, h4, h2, h3, h5⟩

end StratonovichHAMSecondMoment.PhaseBessel
