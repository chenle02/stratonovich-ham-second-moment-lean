module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item A: `E:occupied-multiplication` on the closed Gaussian polynomial spaces and the
closedness of multiplication (Step 1 of the proof of `P:mild-construction`, TeX lines 2178-2201 at
revision edf7085f (book 1.1.3); the display `E:occupied-multiplication` is 2189-2191, the
approximation and closedness sentence 2197-2201).

Proved: `occupied_mult : OccupiedMultTarget.{u, v}` (frozen in `MildInterface`), for every
centered Gaussian field `W : X → Ω → ℝ` on a probability space, with no hypothesis.

Route (as the TeX, with one disclosed difference in the finite-coordinate step):
* Finite coordinates.  The TeX takes `H/‖H‖₂` as the first vector of an orthonormal Gaussian
  basis (2192-2196).  Here a finite family of field values `W(p_1), …, W(p_m)` has the law
  `multivariateGaussian 0 K = stdGaussian.map (√K)` (Mathlib's definition), so a polynomial of
  total degree `≤ n` in the field values is, in law, a polynomial of total degree `≤ n` in `m`
  independent standard Gaussians (`totalDegree_bind₁_le`), and `H` stays a linear form.  The
  bound there is L9's `FockForm.occupied_multiplication` (Hermite creation and annihilation
  operators, the same proof as 2192-2196 in coordinates).  No orthonormalization is needed.
* Spans.  Every element of `span (products of ≤ n field values)` is a polynomial of total
  degree `≤ n` in finitely many field values, every element of `span (field values)` a linear
  form in finitely many field values; two such representations are moved to one common family
  of points (`RepOn.transport`, `LinOn.transport`).
* Closure (2197-2201).  `F ∈ PolyLE n` and `H ∈ LinG` are approximated from the spans (`F`
  first, then `H`); the products are `L²`-Cauchy by the bound; an almost surely convergent
  subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`) identifies the limit with `HF`
  (`ae_limit`).  The same argument is the closedness clause for an arbitrary `H ∈ L²`
  (`mul_closed`).  "The argument allows `F` to depend on `H`" (2201) holds because nothing
  above ties the choice of `F` to `H`.

The probe `L20ProbeA` (never committed) supplied `integral_field_eq`, `occupied_field`,
`totalDegree_bind₁_le` and the linear-substitution lemmas, reproduced here.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface
public import StratonovichHAMSecondMoment.FockForm
public import StratonovichHAMSecondMoment.GaussianHermite

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Real Nat MatrixOrder

namespace StratonovichHAMSecondMoment.MildOccupied

universe u v

open FiniteWick (CenteredGaussianField)
open TerminalWick (prodL2 coeFn_prodL2)
open TerminalWickInputs (fieldL2)
open MildInterface

/-! ### Linear substitutions in polynomials -/

/-- Composition with linear forms does not raise the total degree. -/
theorem totalDegree_bind₁_le {σ τ : Type*} (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (q : MvPolynomial σ ℝ) :
    (MvPolynomial.bind₁ f q).totalDegree ≤ q.totalDegree := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ =>
    (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i))) ?_
  simp only [mul_one]
  exact MvPolynomial.le_totalDegree hs

/-- The linear form `x ↦ Σ_j S_ij x_j` as a polynomial. -/
def linPoly {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) : MvPolynomial (Fin m) ℝ :=
  ∑ j, MvPolynomial.C (S i j) * MvPolynomial.X j

theorem totalDegree_linPoly {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    (linPoly S i).totalDegree ≤ 1 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

theorem eval_linPoly {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) (i : Fin m) :
    MvPolynomial.eval x (linPoly S i) = (S.mulVec x) i := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem eval_bind₁_linPoly {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ)
    (q : MvPolynomial (Fin m) ℝ) :
    MvPolynomial.eval x (MvPolynomial.bind₁ (linPoly S) q) =
      MvPolynomial.eval (S.mulVec x) q := by
  show MvPolynomial.eval₂Hom (RingHom.id ℝ) x (MvPolynomial.bind₁ (linPoly S) q) =
    MvPolynomial.eval₂Hom (RingHom.id ℝ) (S.mulVec x) q
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 2
  funext i
  exact eval_linPoly S x i

/-- `E:occupied-multiplication` (TeX lines 2189-2191 at revision edf7085f (book 1.1.3)) for
standard Gaussians after a linear change of variables `x ↦ S x`: the integrability of the
squared product and the bound. -/
theorem occupied_mulVec {m : ℕ} (n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ)
    (q : MvPolynomial (Fin m) ℝ) (hq : q.totalDegree ≤ n) :
    Integrable (fun x => ((∑ i, b i * (S.mulVec x) i) *
        MvPolynomial.eval (S.mulVec x) q) ^ 2) (GaussianIBP.stdPi m) ∧
      ∫ x, ((∑ i, b i * (S.mulVec x) i) * MvPolynomial.eval (S.mulVec x) q) ^ 2
          ∂GaussianIBP.stdPi m ≤
        4 * ((n : ℝ) + 1) * (∫ x, (∑ i, b i * (S.mulVec x) i) ^ 2 ∂GaussianIBP.stdPi m) *
          ∫ x, (MvPolynomial.eval (S.mulVec x) q) ^ 2 ∂GaussianIBP.stdPi m := by
  set a : Fin m → ℝ := fun j => ∑ i, b i * S i j
  have hH : ∀ x : Fin m → ℝ, ∑ i, b i * (S.mulVec x) i = ∑ j, a j * x j := by
    intro x
    simp only [a, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hF : ∀ x : Fin m → ℝ, MvPolynomial.eval (S.mulVec x) q =
      MvPolynomial.eval x (MvPolynomial.bind₁ (linPoly S) q) := fun x =>
    (eval_bind₁_linPoly S x q).symm
  simp only [hH, hF]
  have h := FockForm.occupied_multiplication n a _
    ((totalDegree_bind₁_le _ (totalDegree_linPoly S) q).trans hq)
  exact ⟨h.1, h.2.2.2⟩

/-! ### Transfer from field values to standard Gaussians -/

section Transfer

variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ}

/-- A continuous functional of finitely many field values is almost everywhere strongly
measurable. -/
theorem aestronglyMeasurable_field {m : ℕ} (hW : CenteredGaussianField W K P) (p : Fin m → X)
    (Φ : (Fin m → ℝ) → ℝ) (hΦ : Continuous Φ) :
    AEStronglyMeasurable (fun ω => Φ (fun i => W (p i) ω)) P := by
  have hc : Continuous fun y : EuclideanSpace ℝ (Fin m) => Φ (WithLp.ofLp y) :=
    hΦ.comp (PiLp.continuous_ofLp 2 _)
  exact hc.comp_aestronglyMeasurable (hW.law m p).aemeasurable.aestronglyMeasurable

/-- **The transfer** (probe A): a continuous functional of finitely many field values
integrates as the same functional of `√K g`, `g` standard Gaussian on `ℝ^m`. -/
theorem integral_field_eq {m : ℕ} (hW : CenteredGaussianField W K P) (p : Fin m → X)
    (Φ : (Fin m → ℝ) → ℝ) (hΦ : Continuous Φ) :
    ∫ ω, Φ (fun i => W (p i) ω) ∂P =
      ∫ x, Φ ((CFC.sqrt (Matrix.of fun a b => K (p a) (p b))).mulVec x)
        ∂GaussianIBP.stdPi m := by
  have hlaw := hW.law m p
  have hc : Continuous fun y : EuclideanSpace ℝ (Fin m) => Φ (WithLp.ofLp y) :=
    hΦ.comp (PiLp.continuous_ofLp 2 _)
  have h1 := hlaw.integral_comp (f := fun y : EuclideanSpace ℝ (Fin m) => Φ (WithLp.ofLp y))
    hc.aestronglyMeasurable
  simp only [Function.comp_def] at h1
  rw [show (fun ω => Φ (fun i => W (p i) ω)) =
      fun ω => Φ (WithLp.ofLp (WithLp.toLp 2 fun a => W (p a) ω)) from rfl, h1,
    multivariateGaussian, integral_map (by fun_prop) hc.aestronglyMeasurable,
    ← map_pi_eq_stdGaussian,
    integral_map (f := fun y : EuclideanSpace ℝ (Fin m) =>
        Φ (WithLp.ofLp (0 + Matrix.toEuclideanCLM (𝕜 := ℝ)
          (CFC.sqrt (Matrix.of fun a b => K (p a) (p b))) y))) (by fun_prop)
      (hc.comp (continuous_const.add (ContinuousLinearMap.continuous _))).aestronglyMeasurable]
  simp [GaussianIBP.stdPi]

/-- The integrability half of the transfer. -/
theorem integrable_field_of {m : ℕ} (hW : CenteredGaussianField W K P) (p : Fin m → X)
    (Φ : (Fin m → ℝ) → ℝ) (hΦ : Continuous Φ)
    (h : Integrable (fun x => Φ ((CFC.sqrt (Matrix.of fun a b => K (p a) (p b))).mulVec x))
      (GaussianIBP.stdPi m)) :
    Integrable (fun ω => Φ (fun i => W (p i) ω)) P := by
  have hlaw := hW.law m p
  have hc : Continuous fun y : EuclideanSpace ℝ (Fin m) => Φ (WithLp.ofLp y) :=
    hΦ.comp (PiLp.continuous_ofLp 2 _)
  have hG : Integrable (fun y : EuclideanSpace ℝ (Fin m) => Φ (WithLp.ofLp y))
      (multivariateGaussian 0 (Matrix.of fun a b => K (p a) (p b))) := by
    rw [multivariateGaussian, integrable_map_measure hc.aestronglyMeasurable (by fun_prop),
      ← map_pi_eq_stdGaussian, integrable_map_measure
        (g := (fun y : EuclideanSpace ℝ (Fin m) => Φ (WithLp.ofLp y)) ∘ fun x =>
          0 + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Matrix.of fun a b => K (p a) (p b))) x)
        (f := WithLp.toLp 2)
        (hc.comp (continuous_const.add (ContinuousLinearMap.continuous _))).aestronglyMeasurable
        (by fun_prop)]
    simpa [Function.comp_def, GaussianIBP.stdPi] using h
  exact hlaw.integrable_comp hG

/-- **`E:occupied-multiplication` for correlated field values** (TeX lines 2189-2191 at
revision edf7085f (book 1.1.3), finite-coordinate part; probe A): for points `p_1, …, p_m`,
`h = Σ b_i W(p_i)` and `f = q(W(p_1), …, W(p_m))`, `q` of total degree `≤ n`, the product `h f`
is square integrable and `E[(hf)²] ≤ 4(n+1) E[h²] E[f²]`. -/
theorem occupied_field [IsProbabilityMeasure P] (hW : CenteredGaussianField W K P) {m : ℕ}
    (n : ℕ) (p : Fin m → X) (b : Fin m → ℝ) (q : MvPolynomial (Fin m) ℝ)
    (hq : q.totalDegree ≤ n) :
    Integrable (fun ω => ((∑ i, b i * W (p i) ω) *
        MvPolynomial.eval (fun i => W (p i) ω) q) ^ 2) P ∧
      ∫ ω, ((∑ i, b i * W (p i) ω) * MvPolynomial.eval (fun i => W (p i) ω) q) ^ 2 ∂P ≤
        4 * ((n : ℝ) + 1) * (∫ ω, (∑ i, b i * W (p i) ω) ^ 2 ∂P) *
          ∫ ω, (MvPolynomial.eval (fun i => W (p i) ω) q) ^ 2 ∂P := by
  have hev : Continuous fun y : Fin m → ℝ => MvPolynomial.eval y q :=
    MvPolynomial.continuous_eval q
  have hlin : Continuous fun y : Fin m → ℝ => ∑ i, b i * y i := by fun_prop
  obtain ⟨hI, hB⟩ := occupied_mulVec n (CFC.sqrt (Matrix.of fun a b => K (p a) (p b))) b q hq
  refine ⟨integrable_field_of hW p (fun y => ((∑ i, b i * y i) * MvPolynomial.eval y q) ^ 2)
    ((hlin.mul hev).pow 2) hI, ?_⟩
  rw [integral_field_eq hW p (fun y => ((∑ i, b i * y i) * MvPolynomial.eval y q) ^ 2)
      ((hlin.mul hev).pow 2),
    integral_field_eq hW p (fun y => (∑ i, b i * y i) ^ 2) (hlin.pow 2),
    integral_field_eq hW p (fun y => (MvPolynomial.eval y q) ^ 2) (hev.pow 2)]
  exact hB

end Transfer

/-! ### Finite representations of the span elements -/

section Rep

variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ}

/-- `F` is (a.s.) a polynomial of total degree `≤ n` in the field values at `p`. -/
def RepOn (W : X → Ω → ℝ) (P : Measure Ω) (n : ℕ) {m : ℕ} (p : Fin m → X)
    (F : Lp ℝ 2 P) : Prop :=
  ∃ q : MvPolynomial (Fin m) ℝ, q.totalDegree ≤ n ∧
    F =ᵐ[P] fun ω => MvPolynomial.eval (fun i => W (p i) ω) q

/-- `H` is (a.s.) a linear combination of the field values at `p`. -/
def LinOn (W : X → Ω → ℝ) (P : Measure Ω) {m : ℕ} (p : Fin m → X) (H : Lp ℝ 2 P) : Prop :=
  ∃ b : Fin m → ℝ, H =ᵐ[P] fun ω => ∑ i, b i * W (p i) ω

theorem RepOn.transport {n m m' : ℕ} {p : Fin m → X} {p' : Fin m' → X} {F : Lp ℝ 2 P}
    (h : RepOn W P n p F) (g : Fin m → Fin m') (hg : ∀ i, p' (g i) = p i) :
    RepOn W P n p' F := by
  obtain ⟨q, hq, hF⟩ := h
  refine ⟨MvPolynomial.rename g q, (MvPolynomial.totalDegree_rename_le g q).trans hq, ?_⟩
  filter_upwards [hF] with ω hω
  rw [hω, MvPolynomial.eval_rename,
    show ((fun i => W (p' i) ω) ∘ g) = fun i => W (p i) ω from funext fun i => by simp [hg]]

theorem LinOn.transport {m m' : ℕ} {p : Fin m → X} {p' : Fin m' → X} {H : Lp ℝ 2 P}
    (h : LinOn W P p H) (g : Fin m → Fin m') (hg : ∀ i, p' (g i) = p i) :
    LinOn W P p' H := by
  classical
  obtain ⟨b, hH⟩ := h
  refine ⟨fun j => ∑ i, if g i = j then b i else 0, ?_⟩
  filter_upwards [hH] with ω hω
  rw [hω]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq]
  simp [hg]

/-- Products of at most `n` field values (the generators of `PolyLE`). -/
theorem repOn_prodL2 (hW : CenteredGaussianField W K P) {n k : ℕ} (hk : k ≤ n)
    (z : Fin k → X) : RepOn W P n z (prodL2 hW z) := by
  refine ⟨∏ i, MvPolynomial.X i, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simp [MvPolynomial.totalDegree_X, hk]
  · filter_upwards [coeFn_prodL2 hW z] with ω hω
    rw [hω]
    simp

/-- Every element of the span of the products of at most `n` field values is a polynomial of
total degree `≤ n` in finitely many field values. -/
theorem exists_repOn (hW : CenteredGaussianField W K P) (n : ℕ) {F : Lp ℝ 2 P}
    (hF : F ∈ Submodule.span ℝ (polyGen hW n)) :
    ∃ (m : ℕ) (p : Fin m → X), RepOn W P n p F := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, z, hk, rfl⟩ := hx
    exact ⟨k, z, repOn_prodL2 hW hk z⟩
  | zero =>
    refine ⟨0, Fin.elim0, 0, by simp, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hω
    rw [hω]
    simp
  | add x y _ _ hx hy =>
    obtain ⟨m₁, p₁, hx⟩ := hx
    obtain ⟨m₂, p₂, hy⟩ := hy
    obtain ⟨q₁, hq₁, h₁⟩ := hx.transport (p' := Fin.append p₁ p₂) (Fin.castAdd m₂)
      (fun i => Fin.append_left p₁ p₂ i)
    obtain ⟨q₂, hq₂, h₂⟩ := hy.transport (p' := Fin.append p₁ p₂) (Fin.natAdd m₁)
      (fun i => Fin.append_right p₁ p₂ i)
    refine ⟨m₁ + m₂, Fin.append p₁ p₂, q₁ + q₂,
      (MvPolynomial.totalDegree_add _ _).trans (max_le hq₁ hq₂), ?_⟩
    filter_upwards [Lp.coeFn_add x y, h₁, h₂] with ω hω e₁ e₂
    rw [hω, Pi.add_apply, e₁, e₂, map_add]
  | smul c x _ hx =>
    obtain ⟨m, p, q, hq, h⟩ := hx
    refine ⟨m, p, c • q, (MvPolynomial.totalDegree_smul_le c q).trans hq, ?_⟩
    filter_upwards [Lp.coeFn_smul c x, h] with ω hω e
    rw [hω, Pi.smul_apply, e, MvPolynomial.smul_eval, smul_eq_mul]

/-- Every element of the span of the field values is a linear combination of finitely many
field values. -/
theorem exists_linOn (hW : CenteredGaussianField W K P) {H : Lp ℝ 2 P}
    (hH : H ∈ Submodule.span ℝ (Set.range (fieldL2 hW))) :
    ∃ (m : ℕ) (p : Fin m → X), LinOn W P p H := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    refine ⟨1, ![y], fun _ => 1, ?_⟩
    filter_upwards [coeFn_prodL2 hW ![y]] with ω hω
    rw [fieldL2, hω]
    simp
  | zero =>
    refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hω
    rw [hω]
    simp
  | add x y _ _ hx hy =>
    obtain ⟨m₁, p₁, hx⟩ := hx
    obtain ⟨m₂, p₂, hy⟩ := hy
    obtain ⟨b₁, h₁⟩ := hx.transport (p' := Fin.append p₁ p₂) (Fin.castAdd m₂)
      (fun i => Fin.append_left p₁ p₂ i)
    obtain ⟨b₂, h₂⟩ := hy.transport (p' := Fin.append p₁ p₂) (Fin.natAdd m₁)
      (fun i => Fin.append_right p₁ p₂ i)
    refine ⟨m₁ + m₂, Fin.append p₁ p₂, b₁ + b₂, ?_⟩
    filter_upwards [Lp.coeFn_add x y, h₁, h₂] with ω hω e₁ e₂
    rw [hω, Pi.add_apply, e₁, e₂, ← Finset.sum_add_distrib]
    simp [add_mul]
  | smul c x _ hx =>
    obtain ⟨m, p, b, h⟩ := hx
    refine ⟨m, p, c • b, ?_⟩
    filter_upwards [Lp.coeFn_smul c x, h] with ω hω e
    rw [hω, Pi.smul_apply, e, smul_eq_mul, Finset.mul_sum]
    simp [mul_assoc]

end Rep

/-! ### The bound on the spans -/

section Span

variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : X → Ω → ℝ} {K : X → X → ℝ}

/-- `E:occupied-multiplication` (TeX lines 2189-2191 at revision edf7085f (book 1.1.3)) for `H`
and `F` represented on one family of points. -/
theorem occupied_rep (hW : CenteredGaussianField W K P) (n : ℕ) {m : ℕ} (p : Fin m → X)
    {H F : Lp ℝ 2 P} (hH : LinOn W P p H) (hF : RepOn W P n p F) :
    MemLp (fun ω => H ω * F ω) 2 P ∧
      ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖ := by
  obtain ⟨b, hb⟩ := hH
  obtain ⟨q, hq, hqF⟩ := hF
  obtain ⟨hI, hB⟩ := occupied_field hW n p b q hq
  have hae : (fun ω => H ω * F ω) =ᵐ[P] fun ω =>
      (∑ i, b i * W (p i) ω) * MvPolynomial.eval (fun i => W (p i) ω) q := by
    filter_upwards [hb, hqF] with ω e₁ e₂
    rw [e₁, e₂]
  have hmeas : AEStronglyMeasurable (fun ω =>
      (∑ i, b i * W (p i) ω) * MvPolynomial.eval (fun i => W (p i) ω) q) P :=
    aestronglyMeasurable_field hW p (fun y => (∑ i, b i * y i) * MvPolynomial.eval y q)
      ((by fun_prop : Continuous fun y : Fin m → ℝ => ∑ i, b i * y i).mul
        (MvPolynomial.continuous_eval q))
  have hM : MemLp (fun ω => H ω * F ω) 2 P :=
    MemLp.ae_eq hae.symm ((memLp_two_iff_integrable_sq hmeas).2 hI)
  refine ⟨hM, ?_⟩
  have hHF : ‖mulL2 H F‖ ^ 2 = ∫ ω, ((∑ i, b i * W (p i) ω) *
      MvPolynomial.eval (fun i => W (p i) ω) q) ^ 2 ∂P := by
    rw [← UniformSeriesTail.integral_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_mulL2 hM, hae] with ω e₁ e₂
    rw [e₁]
    exact congrArg (· ^ 2) e₂
  have hHn : ‖H‖ ^ 2 = ∫ ω, (∑ i, b i * W (p i) ω) ^ 2 ∂P := by
    rw [← UniformSeriesTail.integral_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hb] with ω e
    rw [e]
  have hFn : ‖F‖ ^ 2 = ∫ ω, (MvPolynomial.eval (fun i => W (p i) ω) q) ^ 2 ∂P := by
    rw [← UniformSeriesTail.integral_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hqF] with ω e
    rw [e]
  have hsq : ‖mulL2 H F‖ ^ 2 ≤ (2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hHF, hHn, hFn]
    nlinarith [hB]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- `E:occupied-multiplication` on the spans (before closure). -/
theorem occupied_span (hW : CenteredGaussianField W K P) (n : ℕ) {H F : Lp ℝ 2 P}
    (hH : H ∈ Submodule.span ℝ (Set.range (fieldL2 hW)))
    (hF : F ∈ Submodule.span ℝ (polyGen hW n)) :
    MemLp (fun ω => H ω * F ω) 2 P ∧
      ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖ := by
  obtain ⟨m₁, p₁, h₁⟩ := exists_linOn hW hH
  obtain ⟨m₂, p₂, h₂⟩ := exists_repOn hW n hF
  exact occupied_rep hW n (Fin.append p₁ p₂)
    (h₁.transport (Fin.castAdd m₂) fun i => Fin.append_left p₁ p₂ i)
    (h₂.transport (Fin.natAdd m₁) fun i => Fin.append_right p₁ p₂ i)

end Span

/-! ### Closure -/

section Closure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Identification of the limit** (TeX lines 2199-2200 at revision edf7085f (book 1.1.3)):
if `H_k → H`, `F_k → F` and `H_k F_k → G` in `L²` (all products in `L²`), then `HF = G` almost
surely (an almost surely convergent subsequence of all three). -/
theorem ae_limit {Hk Fk : ℕ → Lp ℝ 2 P} {H F G : Lp ℝ 2 P} (hH : Tendsto Hk atTop (𝓝 H))
    (hF : Tendsto Fk atTop (𝓝 F)) (hm : ∀ k, MemLp (fun ω => Hk k ω * Fk k ω) 2 P)
    (hG : Tendsto (fun k => mulL2 (Hk k) (Fk k)) atTop (𝓝 G)) :
    (fun ω => H ω * F ω) =ᵐ[P] G := by
  obtain ⟨n₁, hn₁, h₁⟩ := (tendstoInMeasure_of_tendsto_Lp hH).exists_seq_tendsto_ae
  obtain ⟨n₂, hn₂, h₂⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hF.comp hn₁.tendsto_atTop)).exists_seq_tendsto_ae
  obtain ⟨n₃, hn₃, h₃⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hG.comp (hn₁.comp hn₂).tendsto_atTop)).exists_seq_tendsto_ae
  have hae : ∀ᵐ ω ∂P, ∀ k, mulL2 (Hk k) (Fk k) ω = Hk k ω * Fk k ω :=
    ae_all_iff.2 fun k => coeFn_mulL2 (hm k)
  filter_upwards [h₁, h₂, h₃, hae] with ω w₁ w₂ w₃ w₄
  have a₁ : Tendsto (fun i => Hk (n₁ (n₂ (n₃ i))) ω) atTop (𝓝 (H ω)) :=
    w₁.comp (hn₂.comp hn₃).tendsto_atTop
  have a₂ : Tendsto (fun i => Fk (n₁ (n₂ (n₃ i))) ω) atTop (𝓝 (F ω)) :=
    w₂.comp hn₃.tendsto_atTop
  have a₃ : Tendsto (fun i => Hk (n₁ (n₂ (n₃ i))) ω * Fk (n₁ (n₂ (n₃ i))) ω) atTop
      (𝓝 (G ω)) := by
    have : Tendsto (fun i => mulL2 (Hk (n₁ (n₂ (n₃ i)))) (Fk (n₁ (n₂ (n₃ i)))) ω) atTop
        (𝓝 (G ω)) := w₃
    simpa only [w₄] using this
  exact tendsto_nhds_unique (a₁.mul a₂) a₃

/-- An almost sure identification `HF = G` gives `HF ∈ L²` and `mulL2 H F = G`. -/
theorem of_ae_eq {H F G : Lp ℝ 2 P} (h : (fun ω => H ω * F ω) =ᵐ[P] G) :
    MemLp (fun ω => H ω * F ω) 2 P ∧ mulL2 H F = G := by
  have hM : MemLp (fun ω => H ω * F ω) 2 P := MemLp.ae_eq h.symm (Lp.memLp G)
  exact ⟨hM, Lp.ext ((coeFn_mulL2 hM).trans h)⟩

/-- **Closedness of multiplication** (TeX lines 2199-2201 at revision edf7085f (book 1.1.3)):
the second clause of `OccupiedMultTarget`, for any `H ∈ L²`. -/
theorem mul_closed (H : Lp ℝ 2 P) (F : ℕ → Lp ℝ 2 P) (F₀ G : Lp ℝ 2 P)
    (hm : ∀ k, MemLp (fun ω => H ω * F k ω) 2 P) (hF : Tendsto F atTop (𝓝 F₀))
    (hG : Tendsto (fun k => mulL2 H (F k)) atTop (𝓝 G)) :
    MemLp (fun ω => H ω * F₀ ω) 2 P ∧ mulL2 H F₀ = G :=
  of_ae_eq (ae_limit (Hk := fun _ => H) tendsto_const_nhds hF hm hG)

theorem mulL2_sub_right {H F F' : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H ω * F ω) 2 P)
    (h₂ : MemLp (fun ω => H ω * F' ω) 2 P) :
    mulL2 H (F - F') = mulL2 H F - mulL2 H F' := by
  have hae : (fun ω => H ω * (F - F') ω) =ᵐ[P] fun ω => H ω * F ω - H ω * F' ω := by
    filter_upwards [Lp.coeFn_sub F F'] with ω hω
    rw [hω, Pi.sub_apply, mul_sub]
  have h₃ : MemLp (fun ω => H ω * (F - F') ω) 2 P := MemLp.ae_eq hae.symm (h₁.sub h₂)
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 h₃, Lp.coeFn_sub (mulL2 H F) (mulL2 H F'), coeFn_mulL2 h₁,
    coeFn_mulL2 h₂, hae] with ω e₁ e₂ e₃ e₄ e₅
  rw [e₁, e₂, Pi.sub_apply, e₃, e₄]
  exact e₅

theorem mulL2_sub_left {H H' F : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H ω * F ω) 2 P)
    (h₂ : MemLp (fun ω => H' ω * F ω) 2 P) :
    mulL2 (H - H') F = mulL2 H F - mulL2 H' F := by
  have hae : (fun ω => (H - H') ω * F ω) =ᵐ[P] fun ω => H ω * F ω - H' ω * F ω := by
    filter_upwards [Lp.coeFn_sub H H'] with ω hω
    rw [hω, Pi.sub_apply, sub_mul]
  have h₃ : MemLp (fun ω => (H - H') ω * F ω) 2 P := MemLp.ae_eq hae.symm (h₁.sub h₂)
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 h₃, Lp.coeFn_sub (mulL2 H F) (mulL2 H' F), coeFn_mulL2 h₁,
    coeFn_mulL2 h₂, hae] with ω e₁ e₂ e₃ e₄ e₅
  rw [e₁, e₂, Pi.sub_apply, e₃, e₄]
  exact e₅

/-- A sequence whose increments are controlled by those of a Cauchy sequence is Cauchy. -/
theorem cauchySeq_of_dist_le {u v : ℕ → Lp ℝ 2 P} {C : ℝ} (hC : 0 ≤ C) (hv : CauchySeq v)
    (h : ∀ i j, dist (u i) (u j) ≤ C * dist (v i) (v j)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff] at hv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hv (ε / (C + 1)) (by positivity)
  refine ⟨N, fun i hi j hj => (h i j).trans_lt ?_⟩
  have hd := hN i hi j hj
  calc C * dist (v i) (v j) ≤ C * (ε / (C + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

end Closure

/-! ### `E:occupied-multiplication` on the closed spaces -/

section Closed

variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : X → Ω → ℝ} {K : X → X → ℝ}

/-- `H` in the span, `F ∈ PolyLE n`: approximate `F` (TeX lines 2197-2200 at revision edf7085f
(book 1.1.3)). -/
theorem occupied_polyLE (hW : CenteredGaussianField W K P) (n : ℕ) {H F : Lp ℝ 2 P}
    (hH : H ∈ Submodule.span ℝ (Set.range (fieldL2 hW))) (hF : F ∈ PolyLE hW n) :
    MemLp (fun ω => H ω * F ω) 2 P ∧
      ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖ := by
  set C := 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ with hCdef
  have hC : 0 ≤ C := by positivity
  have hF' : F ∈ closure (Submodule.span ℝ (polyGen hW n) : Set (Lp ℝ 2 P)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hF
  obtain ⟨Fk, hFk, hlim⟩ := mem_closure_iff_seq_limit.1 hF'
  have hfin := fun k => occupied_span hW n hH (hFk k)
  have hcau : CauchySeq fun k => mulL2 H (Fk k) := by
    refine cauchySeq_of_dist_le hC hlim.cauchySeq fun i j => ?_
    rw [dist_eq_norm, dist_eq_norm, ← mulL2_sub_right (hfin i).1 (hfin j).1]
    exact (occupied_span hW n hH (Submodule.sub_mem _ (hFk i) (hFk j))).2
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcau
  obtain ⟨hM, hEq⟩ := mul_closed H Fk F G (fun k => (hfin k).1) hlim hG
  refine ⟨hM, ?_⟩
  rw [hEq]
  exact le_of_tendsto_of_tendsto' hG.norm (tendsto_const_nhds.mul hlim.norm)
    fun k => (hfin k).2

/-- `H ∈ LinG`, `F ∈ PolyLE n`: approximate `H`. -/
theorem occupied_closed (hW : CenteredGaussianField W K P) (n : ℕ) {H F : Lp ℝ 2 P}
    (hH : H ∈ LinG hW) (hF : F ∈ PolyLE hW n) :
    MemLp (fun ω => H ω * F ω) 2 P ∧
      ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖ := by
  set c := 2 * Real.sqrt ((n : ℝ) + 1)
  have hc : 0 ≤ c := by positivity
  have hH' : H ∈ closure (Submodule.span ℝ (Set.range (fieldL2 hW)) : Set (Lp ℝ 2 P)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hH
  obtain ⟨Hk, hHk, hlim⟩ := mem_closure_iff_seq_limit.1 hH'
  have hfin := fun k => occupied_polyLE hW n (hHk k) hF
  have hcau : CauchySeq fun k => mulL2 (Hk k) F := by
    refine cauchySeq_of_dist_le (C := c * ‖F‖) (by positivity) hlim.cauchySeq fun i j => ?_
    rw [dist_eq_norm, dist_eq_norm, ← mulL2_sub_left (hfin i).1 (hfin j).1]
    have := (occupied_polyLE hW n (Submodule.sub_mem _ (hHk i) (hHk j)) hF).2
    calc _ ≤ c * ‖Hk i - Hk j‖ * ‖F‖ := this
      _ = c * ‖F‖ * ‖Hk i - Hk j‖ := by ring
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcau
  obtain ⟨hM, hEq⟩ := of_ae_eq (ae_limit (Fk := fun _ => F) hlim tendsto_const_nhds
    (fun k => (hfin k).1) hG)
  refine ⟨hM, ?_⟩
  rw [hEq]
  exact le_of_tendsto_of_tendsto' hG.norm
    (((tendsto_const_nhds.mul hlim.norm)).mul tendsto_const_nhds) fun k => (hfin k).2

end Closed

/-- **L20-A: `E:occupied-multiplication` on the closed spaces and the closedness of
multiplication** (Step 1 of the proof of `P:mild-construction`, TeX lines 2187-2201 at revision
edf7085f (book 1.1.3); display 2189-2191, closure 2197-2201), for every centered Gaussian field
on a probability space.  Route difference (module doc): the finite-coordinate bound goes through
the law `multivariateGaussian 0 K = stdGaussian.map (√K)` and L9's
`FockForm.occupied_multiplication` instead of an orthonormal basis starting with `H/‖H‖₂`. -/
theorem occupied_mult : OccupiedMultTarget.{u, v} := by
  intro X Ω _ P _ W K hW
  exact ⟨fun n H hH F hF => occupied_closed hW n hH hF,
    fun H F F₀ G hm hF hG => mul_closed H F F₀ G hm hF hG⟩

end StratonovichHAMSecondMoment.MildOccupied
