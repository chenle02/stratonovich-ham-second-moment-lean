module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Finite slice of Section `S:compact-gaussian` of
`notes/integrated_compact_gaussian.tex` (commit `a284420`): Lemma
`L:gaussian-trace-bounds` (lines 47--90), Proposition `P:finite-gaussian-matrix`
(lines 98--177, including the Hermitian core `E:finite-hermitian-gaussian`,
line 150, and the Hermitian dilation, lines 156--169) and Remark
`R:gaussian-one-variance-test` (lines 179--193).  Lemma
`L:gaussian-scalar-powers` is reused from `GaussianScalarPowers`; the Gaussian
integration by parts is the foundation module `GaussianIBP`.  Nothing is
supplied as a named input: every step, including integration by parts and
polynomial integrability, is proved.

Headline declarations:
* `gaussian_trace_bounds_paper` -- `L:gaussian-trace-bounds` (both displays).
* `finite_hermitian_gaussian`, `finite_hermitian_gaussian_paper` --
  `E:finite-hermitian-gaussian`, `E Tr Y^(2m) ≤ (2m-1)^m Tr D^m`, equality at
  `m = 1`.
* `finite_gaussian_matrix`, `finite_gaussian_matrix_two`,
  `finite_gaussian_matrix_zero`, `finite_gaussian_matrix_paper` --
  `P:finite-gaussian-matrix` (both inequalities, equality at `p = 2`, zero
  families).
* `gaussian_one_variance_test`, `gaussian_one_variance_test_paper` --
  `R:gaussian-one-variance-test` (`288`, `144`, `1224`, `2304`).

Conventions and side conditions made explicit here:
* Matrices are complex, indexed by finite types (`Fin`-indexed in the paper);
  `‖A‖_{S_p}^p = Tr((A^*A)^m)` for `p = 2m` is `schattenPow A m`, the real part
  of that trace (`schattenPow_trace`: the trace is real and nonnegative), and
  `‖A‖_{S_p}` is `schattenNorm A m = (schattenPow A m)^{1/(2m)}`.
* `|Y|` is `CFC.abs Y` and `V^{1/2}` is `CFC.sqrt V` (continuous functional
  calculus, `MatrixOrder`).  Traces that the TeX compares as real numbers are
  compared through `.re`. Only `gaussian_trace_bounds_paper` states the
  vanishing imaginary parts as explicit conclusions; for the other wrappers,
  which bound real parts, the traces are real by the proved lemmas
  `trace_psd`, `trace_mul_pow_im` and `schattenPow_trace`.
* "Independent real standard Gaussians" are `iIndepFun g P` with
  `HasLaw (g k) (gaussianReal 0 1) P` on an arbitrary probability space
  (`_paper` wrappers); the general theorems use their joint law
  `stdPi N = Measure.pi (fun _ => gaussianReal 0 1)`.
* Every expectation conclusion carries the integrability of its integrand
  (the Bochner integral of a non-integrable function is `0` in Lean).
* `p = 2m` with `m ≥ 1` a natural number; `√(p-1)` is `√(2m-1)`; `rpow`
  exponents `1/(2m)`, `1/m`, `(m-1)/m` are applied only to nonnegative bases.

Proof route (same statements as the TeX; differences in the route):
* The trace bounds diagonalize `Y` with Mathlib's spectral theorem; the
  doubly stochastic step diagonalizes `D' = U^* D U` and uses Jensen for
  `t ↦ t^m` (`convexOn_pow`) instead of the tangent-line inequality.
* The derivative of `t ↦ Re Tr(B (Y + t B_k)^j)` is computed in the auxiliary
  normed algebra `NMat n` (matrices with the `L^∞` operator norm), a type
  synonym that avoids the product-topology diamond on `Matrix`.
* Polynomial growth uses the same operator norm; integrability follows from
  `GaussianIBP.integrable_of_growth`.  The integration by parts is applied to
  real parts of traces (real-valued functions), not to complex polynomials.
* The `m = 1` case of `E:finite-hermitian-gaussian` (TeX: "independence gives
  directly") is the same integration-by-parts identity with an empty word.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.GaussianScalarPowers
public import StratonovichHAMSecondMoment.GaussianIBP

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ComplexOrder

namespace StratonovichHAMSecondMoment.FiniteGaussianMatrix

open StratonovichHAMSecondMoment.GaussianIBP

/-! ### Spectral bookkeeping and the two trace bounds -/

section TraceBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary conjugation preserves the trace (auxiliary to the Lean proof route). -/
theorem conj_trace (U : unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    trace ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)) = trace X := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem U.2, Matrix.one_mul]

/-- Powers of a Hermitian matrix in its eigenbasis: `A^k = U diag(λ^k) U^*` (auxiliary to the
Lean proof route). -/
theorem pow_eq_conj {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    A ^ k = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((hA.eigenvalues i : ℂ)) ^ k) *
        star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUs : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hsU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  obtain ⟨ev, hev⟩ : ∃ ev, ev = hA.eigenvalues := ⟨_, rfl⟩
  rw [← hev]
  have hAe : A = U * diagonal (RCLike.ofReal ∘ ev) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [hev, Unitary.conjStarAlgAut_apply]
  induction k with
  | zero => simp [hUs]
  | succ k ih =>
    rw [pow_succ, ih, hAe]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hsU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    congr 3

/-- `Tr A^k = Σ_i λ_i^k` for Hermitian `A` (auxiliary to the Lean proof route). -/
theorem trace_pow_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    trace (A ^ k) = ((∑ i, hA.eigenvalues i ^ k : ℝ) : ℂ) := by
  rw [pow_eq_conj hA k, conj_trace hA.eigenvectorUnitary, trace_diagonal]
  push_cast; rfl

/-- `D' = U^* D U` in the eigenbasis `U` of `Y` (auxiliary to the Lean proof route). -/
def eigConj {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (D : Matrix n n ℂ) : Matrix n n ℂ :=
  star (hY.eigenvectorUnitary : Matrix n n ℂ) * D * hY.eigenvectorUnitary

/-- `D = U D' U^*` with `D' = eigConj hY D` (auxiliary to the Lean proof route). -/
theorem eq_conj_eigConj {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (D : Matrix n n ℂ) :
    D = (hY.eigenvectorUnitary : Matrix n n ℂ) * eigConj hY D *
      star (hY.eigenvectorUnitary : Matrix n n ℂ) := by
  have hUs := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  simp only [eigConj, ← Matrix.mul_assoc, hUs, Matrix.one_mul]
  rw [Matrix.mul_assoc, hUs, Matrix.mul_one]

/-- `U^* D U` is Hermitian when `D` is (auxiliary to the Lean proof route). -/
theorem eigConj_isHermitian {Y D : Matrix n n ℂ} (hY : Y.IsHermitian) (hD : D.IsHermitian) :
    (eigConj hY D).IsHermitian := by
  have := isHermitian_conjTranspose_mul_mul (hY.eigenvectorUnitary : Matrix n n ℂ) hD
  simpa [eigConj, Matrix.star_eq_conjTranspose] using this

/-- `U^* D U` is positive semidefinite when `D` is (auxiliary to the Lean proof route). -/
theorem eigConj_posSemidef {Y D : Matrix n n ℂ} (hY : Y.IsHermitian) (hD : D.PosSemidef) :
    (eigConj hY D).PosSemidef := by
  have := hD.conjTranspose_mul_mul_same (hY.eigenvectorUnitary : Matrix n n ℂ)
  simpa [eigConj, Matrix.star_eq_conjTranspose] using this

/-- Trace of `B diag(a) B diag(b)` as a double sum (auxiliary to the Lean proof route). -/
theorem trace_mul_diag_mul_diag (B : Matrix n n ℂ) (a b : n → ℂ) :
    trace (B * diagonal a * B * diagonal b) = ∑ i, ∑ j, B i j * a j * B j i * b i := by
  simp only [trace, diag, mul_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_diagonal]

/-- The weights `|b_{ij}|^2` of `B` in the eigenbasis of `Y` (TeX line 64) (auxiliary to the
Lean proof route). -/
def eigWeight {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (B : Matrix n n ℂ) (i j : n) : ℝ :=
  Complex.normSq (eigConj hY B i j)

/-- `|b_{ij}| = |b_{ji}|` by Hermitian symmetry (TeX lines 64--65, 71) (auxiliary to the Lean
proof route). -/
theorem eigWeight_symm {Y B : Matrix n n ℂ} (hY : Y.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    eigWeight hY B i j = eigWeight hY B j i := by
  unfold eigWeight
  rw [← (eigConj_isHermitian hY hB).apply i j]
  simp

/-- The eigenbasis formula of the TeX proof (lines 63--68):
`Tr(B Y^q B Y^r) = Σ_{i,j} |b_{ij}|^2 λ_j^q λ_i^r`, a real number (auxiliary to the Lean proof
route). -/
theorem trace_word_eq {B Y : Matrix n n ℂ} (hB : B.IsHermitian) (hY : Y.IsHermitian) (q r : ℕ) :
    trace (B * Y ^ q * B * Y ^ r) =
      ((∑ i, ∑ j, eigWeight hY B i j * hY.eigenvalues j ^ q * hY.eigenvalues i ^ r : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hY.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hsU : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  have hword : B * Y ^ q * B * Y ^ r = U * (eigConj hY B *
      diagonal (fun i => ((hY.eigenvalues i : ℂ)) ^ q) *
      eigConj hY B * diagonal (fun i => ((hY.eigenvalues i : ℂ)) ^ r)) * star U := by
    conv_lhs => rw [pow_eq_conj hY, pow_eq_conj hY, eq_conj_eigConj hY B]
    simp only [Matrix.mul_assoc, ← hU]
    simp only [← Matrix.mul_assoc (star U) U, hsU, Matrix.one_mul]
  rw [hword, conj_trace hY.eigenvectorUnitary, trace_mul_diag_mul_diag]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hji : eigConj hY B j i = star (eigConj hY B i j) := by
    rw [← (eigConj_isHermitian hY hB).apply i j, star_star]
  rw [hji, eigWeight, Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  ring

/-- `Tr(D Y^r) = Σ_i D'_{ii} λ_i^r` in the eigenbasis of `Y` (TeX line 76) (auxiliary to the
Lean proof route). -/
theorem trace_mul_pow_eq {D Y : Matrix n n ℂ} (hY : Y.IsHermitian) (r : ℕ) :
    trace (D * Y ^ r) = ∑ i, eigConj hY D i i * ((hY.eigenvalues i : ℂ)) ^ r := by
  set U : Matrix n n ℂ := (hY.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hsU : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  have hword : D * Y ^ r = U * (eigConj hY D *
      diagonal (fun i => ((hY.eigenvalues i : ℂ)) ^ r)) * star U := by
    conv_lhs => rw [pow_eq_conj hY, eq_conj_eigConj hY D]
    simp only [Matrix.mul_assoc, ← hU]
    simp only [← Matrix.mul_assoc (star U) U, hsU, Matrix.one_mul]
  rw [hword, conj_trace hY.eigenvectorUnitary]
  simp [trace, mul_diagonal]

/-- Trace word bound, core form with even `L` and `Y^L` (auxiliary). -/
theorem trace_word_le {B Y : Matrix n n ℂ} (hB : B.IsHermitian) (hY : Y.IsHermitian)
    {L : ℕ} (hL : Even L) {q : ℕ} (hq : q ≤ L) :
    (trace (B * Y ^ q * B * Y ^ (L - q))).re ≤ (trace (B ^ 2 * Y ^ L)).re := by
  have e2 : B ^ 2 * Y ^ L = B * Y ^ 0 * B * Y ^ L := by simp [sq]
  rw [e2, trace_word_eq hB hY, trace_word_eq hB hY, Complex.ofReal_re, Complex.ofReal_re]
  set ev := hY.eigenvalues
  set w := eigWeight hY B
  have hw0 : ∀ i j, 0 ≤ w i j := fun i j => Complex.normSq_nonneg _
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    have : q = 0 := by omega
    subst this; simp
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hpt : ∀ i j, w i j * ev j ^ q * ev i ^ (L - q) ≤
      w i j * ((q : ℝ) / L * |ev j| ^ L) + w i j * (((L : ℝ) - q) / L * |ev i| ^ L) := by
    intro i j
    have h1 : ev j ^ q * ev i ^ (L - q) ≤ |ev j| ^ q * |ev i| ^ (L - q) := by
      rw [← abs_pow, ← abs_pow, ← abs_mul]; exact le_abs_self _
    have h2 := StratonovichHAMSecondMoment.GaussianScalarPowers.integer_power L q hLpos hq
      (ev j) (ev i)
    rw [mul_assoc, ← mul_add]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (hw0 i j)
  calc ∑ i, ∑ j, w i j * ev j ^ q * ev i ^ (L - q)
      ≤ ∑ i, ∑ j, (w i j * ((q : ℝ) / L * |ev j| ^ L) +
          w i j * (((L : ℝ) - q) / L * |ev i| ^ L)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = (q : ℝ) / L * ∑ i, ∑ j, w i j * |ev j| ^ L +
          ((L : ℝ) - q) / L * ∑ i, ∑ j, w i j * |ev i| ^ L := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_ <;>
          ring
    _ = (q : ℝ) / L * ∑ i, ∑ j, w i j * |ev i| ^ L +
          ((L : ℝ) - q) / L * ∑ i, ∑ j, w i j * |ev i| ^ L := by
        congr 2
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        exact congrArg (· * |ev i| ^ L) (eigWeight_symm hY hB j i)
    _ = ∑ i, ∑ j, w i j * ev j ^ 0 * ev i ^ L := by
        rw [← add_mul, ← add_div, add_sub_cancel, div_self hLR.ne', one_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hL.pow_abs, pow_zero, mul_one]

/-- `Σ_i (D_ii)^m ≤ Tr D^m` for positive semidefinite `D` (auxiliary). -/
theorem sum_diag_pow_le {D : Matrix n n ℂ} (hD : D.PosSemidef) (m : ℕ) :
    ∑ i, (D i i).re ^ m ≤ (trace (D ^ m)).re := by
  have hH := hD.isHermitian
  set W : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hW
  set θ := hH.eigenvalues
  have hθ : ∀ j, 0 ≤ θ j := hD.eigenvalues_nonneg
  have hUs : W * star W = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hsU : star W * W = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hDe : D = W * diagonal (fun j => (θ j : ℂ)) * star W := by
    simpa using pow_eq_conj hH 1
  set w : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hdiag : ∀ i, (D i i).re = ∑ j, w i j * θ j := by
    intro i
    rw [hDe, mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_diagonal, star_apply]
    simp only [RCLike.star_def, w, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hrow : ∀ i, ∑ j, w i j = 1 := by
    intro i
    have := congrFun (congrFun hUs i) i
    rw [mul_apply, one_apply_eq] at this
    have h2 := congrArg Complex.re this
    rw [Complex.re_sum] at h2
    simpa [w, star_apply, Complex.normSq_apply, Complex.mul_re] using h2
  have hcol : ∀ j, ∑ i, w i j = 1 := by
    intro j
    have := congrFun (congrFun hsU j) j
    rw [mul_apply, one_apply_eq] at this
    have h2 := congrArg Complex.re this
    rw [Complex.re_sum] at h2
    simpa [w, star_apply, Complex.normSq_apply, Complex.mul_re] using h2
  have hw0 : ∀ i j, 0 ≤ w i j := fun i j => Complex.normSq_nonneg _
  have hjensen : ∀ i, (∑ j, w i j * θ j) ^ m ≤ ∑ j, w i j * θ j ^ m := by
    intro i
    have := (convexOn_pow m).map_sum_le (t := Finset.univ) (w := w i) (p := θ)
      (fun j _ => hw0 i j) (hrow i) (fun j _ => hθ j)
    simpa [smul_eq_mul] using this
  rw [trace_pow_eq hH, Complex.ofReal_re]
  calc ∑ i, (D i i).re ^ m = ∑ i, (∑ j, w i j * θ j) ^ m := by simp only [hdiag]
    _ ≤ ∑ i, ∑ j, w i j * θ j ^ m := Finset.sum_le_sum fun i _ => hjensen i
    _ = ∑ j, θ j ^ m := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, hcol j, one_mul]

/-- Trace Hölder bound, core form with `Y^(2m-2)` (auxiliary). -/
theorem trace_holder_le {D Y : Matrix n n ℂ} (hD : D.PosSemidef) (hY : Y.IsHermitian)
    {m : ℕ} (hm : 2 ≤ m) :
    (trace (D * Y ^ (2 * m - 2))).re ≤
      (trace (D ^ m)).re ^ (1 / (m : ℝ)) * (trace (Y ^ (2 * m))).re ^ (((m : ℝ) - 1) / m) := by
  set ev := hY.eigenvalues
  set D' := eigConj hY D
  have hD' : D'.PosSemidef := eigConj_posSemidef hY hD
  have hd0 : ∀ i, 0 ≤ (D' i i).re := fun i => by
    have := hD'.diag_nonneg (i := i)
    exact (Complex.nonneg_iff.1 this).1
  have hmR : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (0 : ℝ) < m - 1 := by linarith
  have hlhs : (trace (D * Y ^ (2 * m - 2))).re = ∑ i, (D' i i).re * |ev i| ^ (2 * m - 2) := by
    rw [trace_mul_pow_eq hY, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : Even (2 * m - 2) := ⟨m - 1, by omega⟩
    rw [he.pow_abs, ← Complex.ofReal_pow, Complex.re_mul_ofReal]
  have hY2 : (trace (Y ^ (2 * m))).re = ∑ i, (|ev i| ^ (2 * m - 2)) ^ ((m : ℝ) / (m - 1)) := by
    rw [trace_pow_eq hY, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast (|ev i|), ← Real.rpow_mul (abs_nonneg _)]
    have hexp : ((2 * m - 2 : ℕ) : ℝ) * ((m : ℝ) / (m - 1)) = ((2 * m : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; field_simp
    have he : Even (2 * m) := ⟨m, by ring⟩
    rw [hexp, Real.rpow_natCast, he.pow_abs]
  have hD2 : ∑ i, (D' i i).re ^ (m : ℝ) ≤ (trace (D ^ m)).re := by
    have h1 := sum_diag_pow_le hD' m
    have h2 : trace (D' ^ m) = trace (D ^ m) := by
      have hsU : star (hY.eigenvectorUnitary : Matrix n n ℂ) * hY.eigenvectorUnitary = 1 :=
        Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
      have hpow : ∀ k : ℕ, D ^ k = (hY.eigenvectorUnitary : Matrix n n ℂ) * D' ^ k *
          star (hY.eigenvectorUnitary : Matrix n n ℂ) := by
        intro k
        induction k with
        | zero => simp [Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2]
        | succ k ih =>
          rw [pow_succ, ih, pow_succ]
          conv_lhs => rw [eq_conj_eigConj hY D]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (star _) _, hsU, Matrix.one_mul]
      rw [hpow m, conj_trace]
    simpa only [Real.rpow_natCast, h2] using h1
  rw [hlhs, hY2]
  have hhol := StratonovichHAMSecondMoment.GaussianScalarPowers.finite_holder Finset.univ
    (fun i => (D' i i).re) (fun i => |ev i| ^ (2 * m - 2)) (m : ℝ) hmR
    (fun i _ => hd0 i) (fun i _ => by positivity)
  refine hhol.trans ?_
  have hS0 : 0 ≤ ∑ i, (|ev i| ^ (2 * m - 2)) ^ ((m : ℝ) / (m - 1)) :=
    Finset.sum_nonneg fun i _ => by positivity
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hS0 _)
  exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hd0 i) _) hD2
    (by positivity)

/-- For Hermitian `Y`, even powers of `|Y|` (continuous functional calculus
`CFC.abs`) are even powers of `Y`. -/
theorem abs_pow_even {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (j : ℕ) :
    CFC.abs Y ^ (2 * j) = Y ^ (2 * j) := by
  have h2 : CFC.abs Y ^ 2 = Y ^ 2 := by
    rw [sq, CFC.abs_mul_abs, sq, Matrix.star_eq_conjTranspose, hY.eq]
  rw [pow_mul, pow_mul, h2]

omit [DecidableEq n] in
/-- The trace of a positive semidefinite matrix is real and nonnegative. -/
theorem trace_psd {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (trace M).im = 0 ∧ 0 ≤ (trace M).re := by
  have := Complex.nonneg_iff.1 hM.trace_nonneg
  exact ⟨this.2.symm, this.1⟩

/-- `Tr(D Y^r)` is real for Hermitian `D`, `Y`. -/
theorem trace_mul_pow_im {D Y : Matrix n n ℂ} (hD : D.IsHermitian)
    (hY : Y.IsHermitian) (r : ℕ) : (trace (D * Y ^ r)).im = 0 := by
  rw [trace_mul_pow_eq hY, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := (eigConj_isHermitian hY hD).apply i i
  have him : (eigConj hY D i i).im = 0 := by
    have := congrArg Complex.im h
    simp only [RCLike.star_def, Complex.conj_im] at this
    linarith
  rw [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, him]
  ring

/-- `L:gaussian-trace-bounds` (TeX lines 47--60), with the manuscript's
hypotheses: `B`, `Y` finite Hermitian, `m ≥ 2`, `L = 2m-2`, `0 ≤ q ≤ L`, and
`D ≥ 0` Hermitian (positive semidefinite).  `|Y|` is `CFC.abs Y`.  The traces
on the right are real (their imaginary parts vanish), and the bounds compare
real parts as in the TeX. -/
theorem gaussian_trace_bounds_paper {B Y : Matrix n n ℂ} (hB : B.IsHermitian)
    (hY : Y.IsHermitian) (m : ℕ) (hm : 2 ≤ m) :
    (∀ q : ℕ, q ≤ 2 * m - 2 →
      (trace (B * Y ^ q * B * Y ^ (2 * m - 2 - q))).re ≤
          (trace (B ^ 2 * CFC.abs Y ^ (2 * m - 2))).re ∧
        (trace (B ^ 2 * CFC.abs Y ^ (2 * m - 2))).im = 0) ∧
    (∀ D : Matrix n n ℂ, D.PosSemidef →
      (trace (D * CFC.abs Y ^ (2 * m - 2))).re ≤
          (trace (D ^ m)).re ^ (1 / (m : ℝ)) *
            (trace (CFC.abs Y ^ (2 * m))).re ^ (((m : ℝ) - 1) / m) ∧
        (trace (D * CFC.abs Y ^ (2 * m - 2))).im = 0 ∧ (trace (D ^ m)).im = 0 ∧
        (trace (CFC.abs Y ^ (2 * m))).im = 0) := by
  have hL : 2 * m - 2 = 2 * (m - 1) := by omega
  have habsL : CFC.abs Y ^ (2 * m - 2) = Y ^ (2 * m - 2) := by rw [hL, abs_pow_even hY]
  have habs2 : CFC.abs Y ^ (2 * m) = Y ^ (2 * m) := abs_pow_even hY m
  have hev : Even (2 * m - 2) := ⟨m - 1, by omega⟩
  refine ⟨fun q hq => ⟨?_, ?_⟩, fun D hD => ⟨?_, ?_, (trace_psd (hD.pow m)).1, ?_⟩⟩
  · rw [habsL]; exact trace_word_le hB hY hev hq
  · rw [habsL, trace_mul_pow_im (hB.pow 2) hY]
  · rw [habsL, habs2]; exact trace_holder_le hD hY hm
  · rw [habsL]; exact trace_mul_pow_im hD.isHermitian hY _
  · rw [habs2, trace_pow_eq hY, Complex.ofReal_im]

end TraceBounds

/-! ### Derivative of a noncommutative matrix power -/

/-- Noncommutative derivative of a power along an affine path in a normed algebra:
`d/dt (Y + tC)^k = Σ_{q<k} (Y+tC)^q C (Y+tC)^{k-1-q}` (TeX line 130, "differentiate
the factors in their order") (auxiliary to the Lean proof route). -/
theorem hasDerivAt_pow_affine {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (Y C : 𝔸) (s : ℝ)
    (k : ℕ) :
    HasDerivAt (fun t : ℝ => (Y + t • C) ^ k)
      (∑ q ∈ Finset.range k, (Y + s • C) ^ q * C * (Y + s • C) ^ (k - 1 - q)) s := by
  have hP : HasDerivAt (fun t : ℝ => Y + t • C) C s := by
    simpa using ((hasDerivAt_id s).smul_const C).const_add Y
  induction k with
  | zero => simpa using hasDerivAt_const s (1 : 𝔸)
  | succ k ih =>
    have h := ih.mul hP
    have e : (fun t : ℝ => (Y + t • C) ^ k) * (fun t : ℝ => Y + t • C) =
        fun t => (Y + t • C) ^ (k + 1) := by
      funext t; simp [pow_succ]
    rw [e] at h
    convert h using 1
    rw [Finset.sum_range_succ, Finset.sum_mul]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq : q < k := Finset.mem_range.1 hq
    rw [mul_assoc _ _ ((Y + s • C)), ← pow_succ]
    congr 2
    omega


/-- Type synonym for square complex matrices carrying the `L^∞` operator norm
(auxiliary to the Lean proof route: it avoids the topology diamond with the
product topology on `Matrix`). -/
def NMat (n : Type*) : Type _ := Matrix n n ℂ

section Deriv

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `L^∞` operator norm ring structure on `NMat n` (auxiliary to the Lean proof route). -/
instance instNormedRingNMat : NormedRing (NMat n) := Matrix.linftyOpNormedRing
/-- The real normed algebra structure on `NMat n` (auxiliary to the Lean proof route). -/
instance instNormedAlgebraNMat : NormedAlgebra ℝ (NMat n) := Matrix.linftyOpNormedAlgebra
/-- `NMat n` is finite-dimensional over `ℝ` (auxiliary to the Lean proof route). -/
instance instFiniteDimensionalNMat : FiniteDimensional ℝ (NMat n) :=
  (inferInstance : FiniteDimensional ℝ (Matrix n n ℂ))

/-- `d/dt Re Tr(B (Y + tC)^k) = Σ_{q<k} Re Tr(B Y_t^q C Y_t^{k-1-q})`, `Y_t = Y + tC`
(TeX line 130) (auxiliary to the Lean proof route). -/
theorem hasDerivAt_re_trace_pow (B Y C : Matrix n n ℂ) (k : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (trace (B * (Y + t • C) ^ k)).re)
      (∑ q ∈ Finset.range k,
        (trace (B * ((Y + s • C) ^ q * C * (Y + s • C) ^ (k - 1 - q)))).re) s := by
  let L : Matrix n n ℂ →ₗ[ℝ] ℝ :=
    Complex.reLm.comp (((traceLinearMap n ℂ ℂ).restrictScalars ℝ).comp
      ((LinearMap.mulLeft ℂ B).restrictScalars ℝ))
  let L' : NMat n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (L : NMat n →ₗ[ℝ] ℝ)
  have h1 := hasDerivAt_pow_affine (𝔸 := NMat n) Y C s k
  have h2 := L'.hasFDerivAt.comp_hasDerivAt s h1
  convert h2 using 1
  · rfl
  · symm
    show L (∑ q ∈ Finset.range k,
      ((Y + s • C) ^ q * C * (Y + s • C) ^ (k - 1 - q) : Matrix n n ℂ)) = _
    rw [map_sum]
    rfl

end Deriv

/-! ### Gaussian matrix sums: continuity and polynomial growth -/

section Growth

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Gaussian matrix sum `Σ_k g_k A_k` (the manuscript's `X`, and `Y` for Hermitian `B_k`). -/
def gaussLin {ι : Type*} [Fintype ι] {a b : Type*} (A : ι → Matrix a b ℂ) (g : ι → ℝ) :
    Matrix a b ℂ := ∑ k, g k • A k

/-- Continuity of `g ↦ Re Tr(B Y(g)^j C Y(g)^l)` (auxiliary to the Lean proof route). -/
theorem continuous_word {N : ℕ} (Bs : Fin N → Matrix n n ℂ) (B C : Matrix n n ℂ) (j l : ℕ) :
    Continuous fun g : Fin N → ℝ =>
      (trace (B * (gaussLin Bs g ^ j * C * gaussLin Bs g ^ l))).re := by
  unfold gaussLin
  fun_prop

omit [DecidableEq n] in
/-- An entry is bounded by the `L^∞` operator norm (auxiliary to the Lean proof route). -/
theorem norm_entry_le_linfty (M : Matrix n n ℂ) (i j : n) :
    ‖M i j‖ ≤ @Norm.norm _ (Matrix.linftyOpNormedAddCommGroup).toNorm M := by
  let _ := (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℂ))
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖M i j‖₊ ≤ ∑ j', ‖M i j'‖₊ :=
    Finset.single_le_sum (f := fun j' => ‖M i j'‖₊) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖M i j'‖₊ ≤ Finset.univ.sup fun i => ∑ j', ‖M i j'‖₊ :=
    Finset.le_sup (f := fun i => ∑ j', ‖M i j'‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

/-- Polynomial growth of `g ↦ Re Tr(B Y(g)^j C Y(g)^l)` (TeX lines 122--123, "all
polynomial moments are finite") (auxiliary to the Lean proof route). -/
theorem word_growth {N : ℕ} (Bs : Fin N → Matrix n n ℂ) (B C : Matrix n n ℂ) (j l : ℕ) :
    ∃ K : ℝ, ∀ g : Fin N → ℝ,
      |(trace (B * (gaussLin Bs g ^ j * C * gaussLin Bs g ^ l))).re| ≤ K * (1 + ‖g‖) ^ (j + l) := by
  let _ := (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℂ))
  have : IsBoundedSMul ℝ (Matrix n n ℂ) := Matrix.linftyOpIsBoundedSMul
  have hmul : ∀ X Z : Matrix n n ℂ, ‖X * Z‖ ≤ ‖X‖ * ‖Z‖ := fun X Z => linfty_opNorm_mul X Z
  have hone : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    rw [← diagonal_one, linfty_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
  have hpow : ∀ (X : Matrix n n ℂ) (k : ℕ), ‖X ^ k‖ ≤ ‖X‖ ^ k := by
    intro X k
    induction k with
    | zero => simpa using hone
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (hmul _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
  have htr : ∀ X : Matrix n n ℂ, |(trace X).re| ≤ Fintype.card n * ‖X‖ := by
    intro X
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖X i i‖ ≤ ∑ _i : n, ‖X‖ := Finset.sum_le_sum fun i _ => norm_entry_le_linfty X i i
      _ = Fintype.card n * ‖X‖ := by simp
  set s := ∑ k, ‖Bs k‖
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hG : ∀ g : Fin N → ℝ, ‖gaussLin Bs g‖ ≤ s * (1 + ‖g‖) := by
    intro g
    unfold gaussLin
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    refine (norm_smul_le _ _).trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have := norm_le_pi_norm g k
    linarith [norm_nonneg g]
  refine ⟨Fintype.card n * ‖B‖ * ‖C‖ * s ^ (j + l), fun g => ?_⟩
  refine (htr _).trans ?_
  have hGj : ‖gaussLin Bs g ^ j‖ ≤ (s * (1 + ‖g‖)) ^ j :=
    (hpow _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hG g) j)
  have hGl : ‖gaussLin Bs g ^ l‖ ≤ (s * (1 + ‖g‖)) ^ l :=
    (hpow _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hG g) l)
  have hw : ‖B * (gaussLin Bs g ^ j * C * gaussLin Bs g ^ l)‖ ≤
      ‖B‖ * ((s * (1 + ‖g‖)) ^ j * ‖C‖ * (s * (1 + ‖g‖)) ^ l) := by
    refine (hmul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (hmul _ _).trans ?_
    refine mul_le_mul ((hmul _ _).trans (mul_le_mul_of_nonneg_right hGj (norm_nonneg _))) hGl
      (norm_nonneg _) (by positivity)
  calc (Fintype.card n : ℝ) * ‖B * (gaussLin Bs g ^ j * C * gaussLin Bs g ^ l)‖
      ≤ Fintype.card n * (‖B‖ * ((s * (1 + ‖g‖)) ^ j * ‖C‖ * (s * (1 + ‖g‖)) ^ l)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = Fintype.card n * ‖B‖ * ‖C‖ * s ^ (j + l) * (1 + ‖g‖) ^ (j + l) := by
        rw [mul_pow, mul_pow, pow_add, pow_add]; ring

end Growth

/-! ### Gaussian integration by parts on matrix words -/

section Words

variable {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ} (Bs : Fin N → Matrix n n ℂ)

omit [Fintype n] [DecidableEq n] in
/-- Changing coordinate `k` moves `Y` along `B_k` (auxiliary to the Lean proof route). -/
theorem gaussLin_update (x : Fin N → ℝ) (k : Fin N) (s : ℝ) :
    gaussLin Bs (Function.update x k s) = (gaussLin Bs x - x k • Bs k) + s • Bs k := by
  unfold gaussLin
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ k), Function.update_self,
    Finset.sum_congr rfl (fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])]
  abel

/-- Integrability of matrix words against `stdPi N` (TeX lines 122--126) (auxiliary to the Lean
proof route). -/
theorem integrable_word (B C : Matrix n n ℂ) (j l : ℕ) :
    Integrable (fun x => (trace (B * (gaussLin Bs x ^ j * C * gaussLin Bs x ^ l))).re)
      (stdPi N) := by
  obtain ⟨K, hK⟩ := word_growth Bs B C j l
  exact integrable_of_growth (continuous_word Bs B C j l).aestronglyMeasurable hK

/-- Normalization of a one-factor word (auxiliary to the Lean proof route). -/
theorem word_one (B Y : Matrix n n ℂ) (j : ℕ) : B * (Y ^ j * 1 * Y ^ 0) = B * Y ^ j := by
  simp

/-- Integrability of `Re Tr(B Y^j)` (auxiliary to the Lean proof route). -/
theorem integrable_word_one (B : Matrix n n ℂ) (j : ℕ) :
    Integrable (fun x => (trace (B * gaussLin Bs x ^ j)).re) (stdPi N) := by
  simpa only [word_one] using integrable_word Bs B 1 j 0

/-- Integrability of `g_k Re Tr(B Y^j)` (auxiliary to the Lean proof route). -/
theorem integrable_coord_word_one (k : Fin N) (B : Matrix n n ℂ) (j : ℕ) :
    Integrable (fun x => x k * (trace (B * gaussLin Bs x ^ j)).re) (stdPi N) := by
  obtain ⟨K, hK⟩ := word_growth Bs B 1 j 0
  simp only [word_one] at hK
  have hc := continuous_word Bs B 1 j 0
  simp only [word_one] at hc
  exact integrable_coord_mul_of_growth k hc.aestronglyMeasurable hK

/-- Gaussian integration by parts on a matrix word: differentiating the `j`
factors of `Y^j` in their order. -/
theorem ibp_word (k : Fin N) (B : Matrix n n ℂ) (j : ℕ) :
    ∫ x, x k * (trace (B * gaussLin Bs x ^ j)).re ∂stdPi N =
      ∑ q ∈ Finset.range j, ∫ x, (trace (B * (gaussLin Bs x ^ q * Bs k *
        gaussLin Bs x ^ (j - 1 - q)))).re ∂stdPi N := by
  rw [← integral_finsetSum _ (fun q _ => integrable_word Bs B (Bs k) q (j - 1 - q))]
  refine integral_coord_mul_eq_integral_partial k
    (fun x => (trace (B * gaussLin Bs x ^ j)).re)
    (fun x => ∑ q ∈ Finset.range j, (trace (B * (gaussLin Bs x ^ q * Bs k *
        gaussLin Bs x ^ (j - 1 - q)))).re) (fun x t => ?_)
    (integrable_word_one Bs B j) (integrable_coord_word_one Bs k B j)
    (integrable_finsetSum _ fun q _ => integrable_word Bs B (Bs k) q (j - 1 - q))
  simp only [gaussLin_update]
  exact hasDerivAt_re_trace_pow B (gaussLin Bs x - x k • Bs k) (Bs k) j t

/-- `Tr Y^(j+1) = Σ_k g_k Tr(B_k Y^j)` (TeX line 129) (auxiliary to the Lean proof route). -/
theorem re_trace_pow_succ (x : Fin N → ℝ) (j : ℕ) :
    (trace (gaussLin Bs x ^ (j + 1))).re = ∑ k, x k * (trace (Bs k * gaussLin Bs x ^ j)).re := by
  rw [pow_succ', gaussLin, Finset.sum_mul, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, trace_smul, Complex.real_smul, Complex.re_ofReal_mul]

/-- The integration-by-parts identity of the TeX proof (line 132):
`E Tr Y^(j+1) = Σ_k Σ_{q<j} E Tr(B_k Y^q B_k Y^(j-1-q))`. -/
theorem integral_trace_pow_succ (j : ℕ) :
    ∫ x, (trace (gaussLin Bs x ^ (j + 1))).re ∂stdPi N =
      ∑ k, ∑ q ∈ Finset.range j, ∫ x, (trace (Bs k * (gaussLin Bs x ^ q * Bs k *
        gaussLin Bs x ^ (j - 1 - q)))).re ∂stdPi N := by
  simp only [re_trace_pow_succ]
  rw [integral_finsetSum _ fun k _ => integrable_coord_word_one Bs k (Bs k) j]
  exact Finset.sum_congr rfl fun k _ => ibp_word Bs k (Bs k) j

omit [Fintype n] [DecidableEq n] in
/-- `Y = Σ g_k B_k` is Hermitian for Hermitian `B_k` and real `g_k`. -/
theorem gaussLin_isHermitian (hB : ∀ k, (Bs k).IsHermitian) (x : Fin N → ℝ) :
    (gaussLin Bs x).IsHermitian := by
  unfold gaussLin IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_smul, star_trivial, (hB k).eq]

end Words

/-! ### The Hermitian core `E:finite-hermitian-gaussian` -/

/-- The scalar bootstrap of the TeX proof (lines 147--148): from
`F ≤ c a^{1/m} F^{(m-1)/m}` with `F, a, c ≥ 0` and `m ≥ 2`, deduce `F ≤ c^m a`. -/
theorem bootstrap_scalar {F a c : ℝ} {m : ℕ} (hm : 2 ≤ m) (hF : 0 ≤ F) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (h : F ≤ c * a ^ (1 / (m : ℝ)) * F ^ (((m : ℝ) - 1) / m)) :
    F ≤ c ^ m * a := by
  rcases eq_or_lt_of_le hF with hF0 | hFpos
  · rw [← hF0]; positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsplit : F ^ (1 / (m : ℝ)) * F ^ (((m : ℝ) - 1) / m) = F := by
    rw [← Real.rpow_add hFpos]
    have : 1 / (m : ℝ) + ((m : ℝ) - 1) / m = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  have hr : 0 < F ^ (((m : ℝ) - 1) / m) := Real.rpow_pos_of_pos hFpos _
  have h1 : F ^ (1 / (m : ℝ)) ≤ c * a ^ (1 / (m : ℝ)) := by
    have h' : F ^ (1 / (m : ℝ)) * F ^ (((m : ℝ) - 1) / m) ≤
        c * a ^ (1 / (m : ℝ)) * F ^ (((m : ℝ) - 1) / m) := by rw [hsplit]; exact h
    exact le_of_mul_le_mul_right h' hr
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hF _) h1 m
  have hinv : ∀ b : ℝ, 0 ≤ b → (b ^ (1 / (m : ℝ))) ^ m = b := fun b hb => by
    rw [one_div, Real.rpow_inv_natCast_pow hb (by omega)]
  rw [hinv F hF, mul_pow, hinv a ha] at h2
  exact h2

section Hermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ} (Bs : Fin N → Matrix n n ℂ)

/-- `D = Σ_k B_k^2` is positive semidefinite for Hermitian `B_k`. -/
theorem variance_posSemidef (hB : ∀ k, (Bs k).IsHermitian) :
    (∑ k, Bs k ^ 2).PosSemidef := by
  refine Finset.sum_induction _ PosSemidef (fun _ _ h1 h2 => h1.add h2) PosSemidef.zero
    fun k _ => ?_
  have := posSemidef_conjTranspose_mul_self (Bs k)
  rwa [(hB k).eq, ← sq] at this

/-- `Y^(2m)` is positive semidefinite, so `Tr Y^(2m) ≥ 0` (TeX line 145) (auxiliary to the Lean
proof route). -/
theorem trace_pow_even_psd (hB : ∀ k, (Bs k).IsHermitian) (x : Fin N → ℝ) (m : ℕ) :
    (gaussLin Bs x ^ (2 * m)).PosSemidef := by
  have hY := gaussLin_isHermitian Bs hB x
  have := posSemidef_conjTranspose_mul_self (gaussLin Bs x ^ m)
  rwa [(hY.pow m).eq, ← pow_add, ← two_mul] at this

/-- Integrability of `Re Tr Y^j` against `stdPi N` (TeX lines 122--123). -/
theorem integrable_trace_pow (j : ℕ) :
    Integrable (fun x => (trace (gaussLin Bs x ^ j)).re) (stdPi N) := by
  simpa only [Matrix.one_mul] using integrable_word_one Bs 1 j

/-- First step of the TeX bound (line 140): `F ≤ (2m-1) E Re Tr(D Y^(2m-2))`,
from the integration-by-parts identity and the trace-word bound. -/
theorem integral_trace_pow_le (hB : ∀ k, (Bs k).IsHermitian) (m : ℕ) (hm : 1 ≤ m) :
    ∫ x, (trace (gaussLin Bs x ^ (2 * m))).re ∂stdPi N ≤
      (2 * (m : ℝ) - 1) * ∫ x, (trace ((∑ k, Bs k ^ 2) * gaussLin Bs x ^ (2 * m - 2))).re
        ∂stdPi N := by
  have h2m : 2 * m = (2 * m - 1) + 1 := by omega
  rw [h2m, integral_trace_pow_succ Bs (2 * m - 1), ← h2m]
  have hint : ∀ k, Integrable (fun x => (trace (Bs k ^ 2 * gaussLin Bs x ^ (2 * m - 2))).re)
      (stdPi N) := fun k => integrable_word_one Bs (Bs k ^ 2) (2 * m - 2)
  calc ∑ k, ∑ q ∈ Finset.range (2 * m - 1), ∫ x, (trace (Bs k * (gaussLin Bs x ^ q * Bs k *
          gaussLin Bs x ^ (2 * m - 1 - 1 - q)))).re ∂stdPi N
      ≤ ∑ k, ∑ q ∈ Finset.range (2 * m - 1),
          ∫ x, (trace (Bs k ^ 2 * gaussLin Bs x ^ (2 * m - 2))).re ∂stdPi N := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun q hq => ?_
        refine integral_mono (integrable_word Bs (Bs k) (Bs k) _ _) (hint k) fun x => ?_
        have hqL : q ≤ 2 * m - 2 := by have := Finset.mem_range.1 hq; omega
        have e : 2 * m - 1 - 1 - q = 2 * m - 2 - q := by omega
        simp only [e, ← Matrix.mul_assoc]
        exact trace_word_le (hB k) (gaussLin_isHermitian Bs hB x) ⟨m - 1, by omega⟩ hqL
    _ = (2 * (m : ℝ) - 1) * ∑ k,
          ∫ x, (trace (Bs k ^ 2 * gaussLin Bs x ^ (2 * m - 2))).re ∂stdPi N := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
        congr 1; funext k; congr 1
        rw [Nat.cast_sub (by omega)]; push_cast; ring
    _ = (2 * (m : ℝ) - 1) * ∫ x, (trace ((∑ k, Bs k ^ 2) * gaussLin Bs x ^ (2 * m - 2))).re
          ∂stdPi N := by
        rw [← integral_finsetSum _ fun k _ => hint k]
        congr 1; congr 1; funext x
        rw [Finset.sum_mul, trace_sum, Complex.re_sum]

/-- `E:finite-hermitian-gaussian` at `m = 1`, as an equality:
`E Re Tr Y^2 = Re Tr D` (the TeX derives it from independence; here it is the
same integration-by-parts identity with an empty word). -/
theorem integral_trace_sq_eq :
    ∫ x, (trace (gaussLin Bs x ^ 2)).re ∂stdPi N = (trace (∑ k, Bs k ^ 2)).re := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, integral_trace_pow_succ Bs 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.sub_self, Matrix.one_mul,
    Matrix.mul_one, integral_const, probReal_univ, one_smul, trace_sum, Complex.re_sum]
  simp [sq]

/-- `E:finite-hermitian-gaussian`: for Hermitian `B_k`, `Y = Σ g_k B_k`,
`D = Σ B_k^2` and `m ≥ 1`, `E Tr Y^(2m) ≤ (2m-1)^m Tr D^m` (with integrability;
traces are real, written with `.re`). -/
theorem finite_hermitian_gaussian (hB : ∀ k, (Bs k).IsHermitian) (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun x => (trace (gaussLin Bs x ^ (2 * m))).re) (stdPi N) ∧
      ∫ x, (trace (gaussLin Bs x ^ (2 * m))).re ∂stdPi N ≤
        (2 * (m : ℝ) - 1) ^ m * (trace ((∑ k, Bs k ^ 2) ^ m)).re := by
  refine ⟨integrable_trace_pow Bs (2 * m), ?_⟩
  rcases eq_or_lt_of_le hm with h1 | h2
  · subst h1
    rw [integral_trace_sq_eq]; norm_num
  have hm2 : 2 ≤ m := h2
  set D := ∑ k, Bs k ^ 2 with hD
  have hDpsd : D.PosSemidef := variance_posSemidef Bs hB
  set F := ∫ x, (trace (gaussLin Bs x ^ (2 * m))).re ∂stdPi N with hFdef
  set a := (trace (D ^ m)).re
  have ha : 0 ≤ a := (trace_psd (hDpsd.pow m)).2
  set r : ℝ := ((m : ℝ) - 1) / m
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr0 : 0 < r := div_pos (by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith) hm0
  have hr1 : r < 1 := (div_lt_one hm0).2 (by linarith)
  have hZnn : 0 ≤ᵐ[stdPi N] fun x => (trace (gaussLin Bs x ^ (2 * m))).re :=
    Filter.Eventually.of_forall fun x => (trace_psd (trace_pow_even_psd Bs hB x m)).2
  obtain ⟨hZr, hEZr⟩ := StratonovichHAMSecondMoment.GaussianScalarPowers.expectation_rpow_le
    (stdPi N) _ (integrable_trace_pow Bs (2 * m)) hZnn r hr0 hr1
  have hstep2 : ∫ x, (trace (D * gaussLin Bs x ^ (2 * m - 2))).re ∂stdPi N ≤
      a ^ (1 / (m : ℝ)) * F ^ r := by
    calc ∫ x, (trace (D * gaussLin Bs x ^ (2 * m - 2))).re ∂stdPi N
        ≤ ∫ x, a ^ (1 / (m : ℝ)) * (trace (gaussLin Bs x ^ (2 * m))).re ^ r ∂stdPi N :=
          integral_mono (integrable_word_one Bs D _) (hZr.const_mul _) fun x =>
            trace_holder_le hDpsd (gaussLin_isHermitian Bs hB x) hm2
      _ = a ^ (1 / (m : ℝ)) * ∫ x, (trace (gaussLin Bs x ^ (2 * m))).re ^ r ∂stdPi N :=
          integral_const_mul _ _
      _ ≤ a ^ (1 / (m : ℝ)) * F ^ r :=
          mul_le_mul_of_nonneg_left hEZr (Real.rpow_nonneg ha _)
  have hF0 : 0 ≤ F := integral_nonneg_of_ae hZnn
  have hc : (0 : ℝ) ≤ 2 * m - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith
  refine bootstrap_scalar hm2 hF0 ha hc ?_
  calc F ≤ (2 * (m : ℝ) - 1) * ∫ x, (trace (D * gaussLin Bs x ^ (2 * m - 2))).re ∂stdPi N :=
        integral_trace_pow_le Bs hB m hm
    _ ≤ (2 * (m : ℝ) - 1) * (a ^ (1 / (m : ℝ)) * F ^ r) := mul_le_mul_of_nonneg_left hstep2 hc
    _ = _ := by ring

end Hermitian

/-! ### Rectangular matrices: Schatten powers and the Hermitian dilation -/

section Dilation

variable {o n : Type*} [Fintype o] [Fintype n] [DecidableEq o] [DecidableEq n]

/-- The manuscript's `‖M‖_{S_p}^p = Tr((M^* M)^m)` for even `p = 2m` (a real number;
`schattenPow_trace` shows the trace is real and nonnegative). -/
def schattenPow (M : Matrix o n ℂ) (m : ℕ) : ℝ := (trace ((Mᴴ * M) ^ m)).re

/-- The Schatten norm `‖M‖_{S_p} = (Tr((M^* M)^m))^{1/p}`, `p = 2m`. -/
def schattenNorm (M : Matrix o n ℂ) (m : ℕ) : ℝ := schattenPow M m ^ (1 / (2 * (m : ℝ)))

omit [DecidableEq o] in
/-- `Tr((M^* M)^m)` is real and nonnegative. -/
theorem schattenPow_trace (M : Matrix o n ℂ) (m : ℕ) :
    trace ((Mᴴ * M) ^ m) = (schattenPow M m : ℂ) ∧ 0 ≤ schattenPow M m := by
  obtain ⟨him, hre⟩ := trace_psd ((posSemidef_conjTranspose_mul_self M).pow m)
  exact ⟨Complex.ext (by simp [schattenPow]) (by simp [him]), hre⟩

/-- The output variance `V_out = Σ_k A_k A_k^*`. -/
def vOut {N : ℕ} (A : Fin N → Matrix o n ℂ) : Matrix o o ℂ := ∑ k, A k * (A k)ᴴ

/-- The input variance `V_in = Σ_k A_k^* A_k`. -/
def vIn {N : ℕ} (A : Fin N → Matrix o n ℂ) : Matrix n n ℂ := ∑ k, (A k)ᴴ * A k

/-- The Hermitian dilation `[[0, M], [M^*, 0]]`. -/
def dil (M : Matrix o n ℂ) : Matrix (o ⊕ n) (o ⊕ n) ℂ := fromBlocks 0 M Mᴴ 0

omit [Fintype o] [Fintype n] [DecidableEq o] [DecidableEq n] in
/-- The dilation is Hermitian (TeX line 156). -/
theorem dil_isHermitian (M : Matrix o n ℂ) : (dil M).IsHermitian := by
  simp [dil, IsHermitian, fromBlocks_conjTranspose]

omit [Fintype o] [Fintype n] [DecidableEq o] [DecidableEq n] in
/-- `Σ g_k dil(A_k) = dil(Σ g_k A_k)` (TeX lines 157--159). -/
theorem gaussLin_dil {N : ℕ} (A : Fin N → Matrix o n ℂ) (x : Fin N → ℝ) :
    gaussLin (fun k => dil (A k)) x = dil (gaussLin A x) := by
  ext (i | i) (j | j) <;>
    simp [gaussLin, dil, Matrix.sum_apply, conjTranspose_apply, fromBlocks]

/-- `dil(M)^2 = diag(M M^*, M^* M)` (auxiliary to the Lean proof route). -/
theorem dil_sq (M : Matrix o n ℂ) : dil M ^ 2 = fromBlocks (M * Mᴴ) 0 0 (Mᴴ * M) := by
  simp [dil, sq, fromBlocks_multiply]

/-- Powers of a block-diagonal matrix (auxiliary to the Lean proof route). -/
theorem fromBlocks_diag_pow (P : Matrix o o ℂ) (Q : Matrix n n ℂ) (k : ℕ) :
    fromBlocks P 0 0 Q ^ k = fromBlocks (P ^ k) 0 0 (Q ^ k) := by
  induction k with
  | zero => simp [fromBlocks_one]
  | succ k ih => rw [pow_succ, ih, fromBlocks_multiply]; simp [pow_succ]

omit [DecidableEq o] [DecidableEq n] in
/-- The trace of a block matrix is the sum of the traces of its diagonal blocks (auxiliary to
the Lean proof route). -/
theorem trace_fromBlocks (P : Matrix o o ℂ) (Q : Matrix o n ℂ) (R : Matrix n o ℂ)
    (S : Matrix n n ℂ) : trace (fromBlocks P Q R S) = trace P + trace S := by
  simp [trace, Fintype.sum_sum_type]

/-- `M (M^*M)^k = (MM^*)^k M` (TeX line 164) (auxiliary to the Lean proof route). -/
theorem mul_conj_pow_mul (M : Matrix o n ℂ) (k : ℕ) :
    M * (Mᴴ * M) ^ k = (M * Mᴴ) ^ k * M := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, pow_succ, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc]

/-- `Tr((MM^*)^m) = Tr((M^*M)^m)` for `m ≥ 1` (TeX lines 162--164). -/
theorem trace_mul_conj_pow (M : Matrix o n ℂ) {m : ℕ} (hm : 1 ≤ m) :
    trace ((M * Mᴴ) ^ m) = trace ((Mᴴ * M) ^ m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ, ← Matrix.mul_assoc, ← mul_conj_pow_mul, Matrix.mul_assoc, trace_mul_comm,
    Matrix.mul_assoc, ← pow_succ]

/-- `Tr dil(M)^(2m) = 2 Tr((M^*M)^m)` for `m ≥ 1` (TeX line 166). -/
theorem trace_dil_pow (M : Matrix o n ℂ) {m : ℕ} (hm : 1 ≤ m) :
    (trace (dil M ^ (2 * m))).re = 2 * schattenPow M m := by
  rw [pow_mul, dil_sq, fromBlocks_diag_pow, trace_fromBlocks, trace_mul_conj_pow M hm,
    schattenPow, Complex.add_re]
  ring

/-- `D = Σ_k dil(A_k)^2 = diag(V_out, V_in)` (TeX line 160). -/
theorem sum_dil_sq {N : ℕ} (A : Fin N → Matrix o n ℂ) :
    ∑ k, dil (A k) ^ 2 = fromBlocks (vOut A) 0 0 (vIn A) := by
  simp only [dil_sq]
  ext (i | i) (j | j) <;> simp [vOut, vIn, Matrix.sum_apply, fromBlocks]

/-- `Tr D^m = Tr V_out^m + Tr V_in^m` (TeX lines 167--168). -/
theorem trace_variance_pow {N : ℕ} (A : Fin N → Matrix o n ℂ) (m : ℕ) :
    (trace ((∑ k, dil (A k) ^ 2) ^ m)).re =
      (trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re := by
  rw [sum_dil_sq, fromBlocks_diag_pow, trace_fromBlocks, Complex.add_re]

omit [DecidableEq o] [DecidableEq n] in
/-- `V_out` is positive semidefinite. -/
theorem vOut_posSemidef {N : ℕ} (A : Fin N → Matrix o n ℂ) : (vOut A).PosSemidef :=
  Finset.sum_induction _ PosSemidef (fun _ _ h1 h2 => h1.add h2) PosSemidef.zero
    fun k _ => posSemidef_self_mul_conjTranspose (A k)

omit [DecidableEq o] [DecidableEq n] in
/-- `V_in` is positive semidefinite. -/
theorem vIn_posSemidef {N : ℕ} (A : Fin N → Matrix o n ℂ) : (vIn A).PosSemidef :=
  Finset.sum_induction _ PosSemidef (fun _ _ h1 h2 => h1.add h2) PosSemidef.zero
    fun k _ => posSemidef_conjTranspose_mul_self (A k)

omit [DecidableEq o] [DecidableEq n] in
/-- `Tr V_out = Tr V_in` (trace cyclicity for rectangular matrices). -/
theorem trace_vOut_eq_trace_vIn {N : ℕ} (A : Fin N → Matrix o n ℂ) :
    trace (vOut A) = trace (vIn A) := by
  simp only [vOut, vIn, trace_sum]
  exact Finset.sum_congr rfl fun k _ => trace_mul_comm _ _

/-- For positive semidefinite `V`, `‖V^{1/2}‖_{S_p} = (Tr V^m)^{1/p}`, `p = 2m`
(`V^{1/2}` is the continuous-functional-calculus square root `CFC.sqrt`). -/
theorem schattenNorm_sqrt {V : Matrix o o ℂ} (hV : V.PosSemidef) (m : ℕ) :
    schattenNorm (CFC.sqrt V) m = (trace (V ^ m)).re ^ (1 / (2 * (m : ℝ))) := by
  have h0 : 0 ≤ V := hV.nonneg
  have hs : (CFC.sqrt V)ᴴ = CFC.sqrt V := (CFC.sqrt_nonneg V).isSelfAdjoint.star_eq
  rw [schattenNorm, schattenPow, hs, CFC.sqrt_mul_sqrt_self V h0]

end Dilation

/-! ### `P:finite-gaussian-matrix` on `stdPi N` -/

section Rect

variable {o n : Type*} [Fintype o] [Fintype n] [DecidableEq o] [DecidableEq n] {N : ℕ}
  (A : Fin N → Matrix o n ℂ)

/-- `‖X‖_{S_p}^p` is integrable against `stdPi N`. -/
theorem integrable_schattenPow (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun x => schattenPow (gaussLin A x) m) (stdPi N) := by
  have h := integrable_trace_pow (fun k => dil (A k)) (2 * m)
  simp only [gaussLin_dil, trace_dil_pow _ hm] at h
  simpa using h.div_const 2

/-- The Hermitian core applied to the dilation: `E ‖X‖_{S_p}^p ≤ (2m-1)^m (Tr V_out^m + Tr
V_in^m)/2`. -/
theorem integral_schattenPow_le (m : ℕ) (hm : 1 ≤ m) :
    ∫ x, schattenPow (gaussLin A x) m ∂stdPi N ≤
      (2 * (m : ℝ) - 1) ^ m * (((trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re) / 2) := by
  have h := (finite_hermitian_gaussian (fun k => dil (A k)) (fun k => dil_isHermitian (A k))
    m hm).2
  simp only [gaussLin_dil, trace_dil_pow _ hm, trace_variance_pow] at h
  rw [integral_const_mul] at h
  linarith

/-- At `p = 2`: `E ‖X‖_{S_2}^2 = (Tr V_out + Tr V_in)/2` (TeX lines 173--175). -/
theorem integral_schattenPow_one :
    ∫ x, schattenPow (gaussLin A x) 1 ∂stdPi N =
      ((trace (vOut A ^ 1)).re + (trace (vIn A ^ 1)).re) / 2 := by
  have h := integral_trace_sq_eq (fun k => dil (A k))
  have e : ∀ x : Fin N → ℝ, (trace (gaussLin (fun k => dil (A k)) x ^ 2)).re =
      2 * schattenPow (gaussLin A x) 1 := fun x => by
    rw [gaussLin_dil, ← trace_dil_pow _ le_rfl]
  simp only [e, integral_const_mul] at h
  rw [← pow_one (∑ k, dil (A k) ^ 2), trace_variance_pow] at h
  linarith

/-- `P:finite-gaussian-matrix` (TeX lines 98--118), on the canonical space
`stdPi N` of `N` independent standard Gaussians: for `p = 2m ≥ 2`,
`(E ‖X‖_{S_p}^p)^{1/p} ≤ √(p-1) ((Tr V_out^m + Tr V_in^m)/2)^{1/p}
≤ √(p-1) max(‖V_out^{1/2}‖_{S_p}, ‖V_in^{1/2}‖_{S_p})`, with integrability. -/
theorem finite_gaussian_matrix (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun x => schattenPow (gaussLin A x) m) (stdPi N) ∧
      (∫ x, schattenPow (gaussLin A x) m ∂stdPi N) ^ (1 / (2 * (m : ℝ))) ≤
        √(2 * (m : ℝ) - 1) *
          (((trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re) / 2) ^ (1 / (2 * (m : ℝ))) ∧
      √(2 * (m : ℝ) - 1) *
          (((trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re) / 2) ^ (1 / (2 * (m : ℝ))) ≤
        √(2 * (m : ℝ) - 1) *
          max (schattenNorm (CFC.sqrt (vOut A)) m) (schattenNorm (CFC.sqrt (vIn A)) m) := by
  set a := (trace (vOut A ^ m)).re
  set b := (trace (vIn A ^ m)).re
  have ha : 0 ≤ a := (trace_psd ((vOut_posSemidef A).pow m)).2
  have hb : 0 ≤ b := (trace_psd ((vIn_posSemidef A).pow m)).2
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : (0 : ℝ) ≤ 2 * m - 1 := by linarith
  have he : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
  have hE0 : 0 ≤ ∫ x, schattenPow (gaussLin A x) m ∂stdPi N :=
    integral_nonneg fun x => (schattenPow_trace _ m).2
  refine ⟨integrable_schattenPow A m hm, ?_, ?_⟩
  · calc (∫ x, schattenPow (gaussLin A x) m ∂stdPi N) ^ (1 / (2 * (m : ℝ)))
        ≤ ((2 * (m : ℝ) - 1) ^ m * ((a + b) / 2)) ^ (1 / (2 * (m : ℝ))) :=
          Real.rpow_le_rpow hE0 (integral_schattenPow_le A m hm) he.le
      _ = √(2 * (m : ℝ) - 1) * ((a + b) / 2) ^ (1 / (2 * (m : ℝ))) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hc, Real.sqrt_eq_rpow]
          congr 2
          field_simp
  · refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [schattenNorm_sqrt (vOut_posSemidef A), schattenNorm_sqrt (vIn_posSemidef A)]
    rcases le_total a b with hab | hab
    · rw [max_eq_right (Real.rpow_le_rpow ha hab he.le)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) he.le
    · rw [max_eq_left (Real.rpow_le_rpow hb hab he.le)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) he.le

/-- Equality at `p = 2`: `E ‖X‖_{S_2}^2 = Tr V_in = Tr V_out`, so the first
inequality of `P:finite-gaussian-matrix` is an equality at `m = 1`. -/
theorem finite_gaussian_matrix_two :
    ∫ x, schattenPow (gaussLin A x) 1 ∂stdPi N = (trace (vIn A)).re ∧
      (trace (vOut A)).re = (trace (vIn A)).re ∧
      (∫ x, schattenPow (gaussLin A x) 1 ∂stdPi N) ^ (1 / (2 * ((1 : ℕ) : ℝ))) =
        √(2 * ((1 : ℕ) : ℝ) - 1) *
          (((trace (vOut A ^ 1)).re + (trace (vIn A ^ 1)).re) / 2) ^ (1 / (2 * ((1 : ℕ) : ℝ))) := by
  have h1 := integral_schattenPow_one A
  have h2 : (trace (vOut A)).re = (trace (vIn A)).re := by rw [trace_vOut_eq_trace_vIn]
  refine ⟨by rw [h1]; simp [h2], h2, ?_⟩
  rw [h1]; norm_num

/-- Empty or zero families give the zero identity (TeX line 117): if every
`A_k = 0` (in particular if `N = 0`), then `E ‖X‖_{S_p}^p = 0`, the average
`(Tr V_out^m + Tr V_in^m)/2` is `0`, and both `‖V^{1/2}‖_{S_p}` vanish. -/
theorem finite_gaussian_matrix_zero (hA : ∀ k, A k = 0) (m : ℕ) (hm : 1 ≤ m) :
    ∫ x, schattenPow (gaussLin A x) m ∂stdPi N = 0 ∧
      ((trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re) / 2 = 0 ∧
      schattenNorm (CFC.sqrt (vOut A)) m = 0 ∧ schattenNorm (CFC.sqrt (vIn A)) m = 0 := by
  have hm0 : m ≠ 0 := by omega
  have hX : ∀ x, gaussLin A x = 0 := fun x => by simp [gaussLin, hA]
  have hO : vOut A = 0 := by simp [vOut, hA]
  have hI : vIn A = 0 := by simp [vIn, hA]
  have hz : ∀ k : ℕ, k ≠ 0 → schattenPow (0 : Matrix o n ℂ) k = 0 := fun k hk => by
    simp [schattenPow, zero_pow hk]
  have he : (1 / (2 * (m : ℝ))) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    positivity
  refine ⟨by simp [hX, hz m hm0], by simp [hO, hI, zero_pow hm0], ?_, ?_⟩
  · rw [hO, CFC.sqrt_zero, schattenNorm]
    simp only [schattenPow, conjTranspose_zero, Matrix.mul_zero, zero_pow hm0, trace_zero,
      Complex.zero_re, Real.zero_rpow he]
  · rw [hI, CFC.sqrt_zero, schattenNorm]
    simp only [schattenPow, conjTranspose_zero, Matrix.mul_zero, zero_pow hm0, trace_zero,
      Complex.zero_re, Real.zero_rpow he]

end Rect

/-! ### `R:gaussian-one-variance-test` -/

section OneVariance

/-- Coordinate row matrices `A_k = e_k^T` (`1 × n`). -/
def rowFamily (n : ℕ) : Fin n → Matrix (Fin 1) (Fin n) ℂ :=
  fun k => of fun _ j => if j = k then 1 else 0

/-- The transposed family of coordinate columns `e_k` (`n × 1`). -/
def colFamily (n : ℕ) : Fin n → Matrix (Fin n) (Fin 1) ℂ :=
  fun k => of fun i _ => if i = k then 1 else 0

/-- `X = (g_1, …, g_n)` as a row (TeX line 181) (auxiliary to the Lean proof route). -/
theorem gaussLin_rowFamily {n : ℕ} (x : Fin n → ℝ) :
    gaussLin (rowFamily n) x = of fun _ j => (x j : ℂ) := by
  ext a j
  simp [gaussLin, rowFamily, Matrix.sum_apply]

/-- The transposed `X` as a column (auxiliary to the Lean proof route). -/
theorem gaussLin_colFamily {n : ℕ} (x : Fin n → ℝ) :
    gaussLin (colFamily n) x = of fun i _ => (x i : ℂ) := by
  ext i a
  simp [gaussLin, colFamily, Matrix.sum_apply]

/-- `X X^* = Σ_k g_k^2` (a `1 × 1` matrix), for every `n` and every real `x`.
Informally, `X` then has at most one nonzero singular value, equal to
`(Σ_k g_k^2)^{1/2}` when `x ≠ 0`; this consequence is not part of the
statement. -/
theorem rowFamily_mul_conj {n : ℕ} (x : Fin n → ℝ) :
    gaussLin (rowFamily n) x * (gaussLin (rowFamily n) x)ᴴ =
      of fun _ _ => ((∑ j, x j ^ 2 : ℝ) : ℂ) := by
  ext a b
  simp [gaussLin_rowFamily, mul_apply, sq]

/-- `X^* X = Σ_k g_k^2` for the transposed family (auxiliary to the Lean proof route). -/
theorem colFamily_conj_mul {n : ℕ} (x : Fin n → ℝ) :
    (gaussLin (colFamily n) x)ᴴ * gaussLin (colFamily n) x =
      of fun _ _ => ((∑ j, x j ^ 2 : ℝ) : ℂ) := by
  ext a b
  simp [gaussLin_colFamily, mul_apply, sq]

/-- `Tr [s]^2 = s^2` for a `1 × 1` matrix (auxiliary to the Lean proof route). -/
theorem one_by_one_sq (s : ℝ) :
    (trace ((of fun _ _ => (s : ℂ) : Matrix (Fin 1) (Fin 1) ℂ) ^ 2)).re = s ^ 2 := by
  simp [sq, trace, mul_apply]

/-- `‖X‖_{S_4}^4 = (Σ_k g_k^2)^2` (TeX lines 182--185). -/
theorem schattenPow_rowFamily {n : ℕ} (x : Fin n → ℝ) :
    schattenPow (gaussLin (rowFamily n) x) 2 = (∑ j, x j ^ 2) ^ 2 := by
  rw [schattenPow, ← trace_mul_conj_pow _ (by norm_num), rowFamily_mul_conj, one_by_one_sq]

/-- `‖X‖_{S_4}^4 = (Σ_k g_k^2)^2` for the transposed family. -/
theorem schattenPow_colFamily {n : ℕ} (x : Fin n → ℝ) :
    schattenPow (gaussLin (colFamily n) x) 2 = (∑ j, x j ^ 2) ^ 2 := by
  rw [schattenPow, colFamily_conj_mul, one_by_one_sq]

/-- `E[g_j^2 g_l^2] = 3` if `j = l` and `1` otherwise (from `E g^2 = 1`,
`E g^4 = 3` and independence), with integrability. -/
theorem integral_sq_mul_sq {n : ℕ} (j l : Fin n) :
    Integrable (fun x : Fin n → ℝ => x j ^ 2 * x l ^ 2) (stdPi n) ∧
      ∫ x, x j ^ 2 * x l ^ 2 ∂stdPi n = if j = l then 3 else 1 := by
  set e : Fin n → ℕ := fun i => (if i = j then 2 else 0) + (if i = l then 2 else 0)
  have hprod : ∀ x : Fin n → ℝ, x j ^ 2 * x l ^ 2 = ∏ i, x i ^ e i := by
    intro x
    simp only [e, pow_add, Finset.prod_mul_distrib, pow_ite, pow_zero, Fintype.prod_ite_eq']
  have hfun : (fun x : Fin n → ℝ => x j ^ 2 * x l ^ 2) = fun x => ∏ i, x i ^ e i :=
    funext hprod
  have hint : Integrable (fun x : Fin n → ℝ => ∏ i, x i ^ e i) (stdPi n) :=
    Integrable.fintype_prod (f := fun i (t : ℝ) => t ^ e i)
      (fun i => integrable_pow_gaussian (e i))
  refine ⟨hfun ▸ hint, ?_⟩
  rw [hfun]
  have h1 := integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun i (t : ℝ) => t ^ e i)
    (μ := fun _ => gaussianReal 0 1)
  unfold stdPi
  rw [h1]
  have hi : ∀ i, ∫ t, t ^ e i ∂gaussianReal 0 1 = if i = j ∧ i = l then 3 else 1 := by
    intro i
    rcases eq_or_ne i j with rfl | hj <;> rcases eq_or_ne i l with rfl | hl
    · simp [e, moment_four]
    · simp [e, hl, moment_two]
    · simp [e, hj, moment_two]
    · simp [e, hj, hl]
  simp only [hi]
  by_cases hjl : j = l
  · subst hjl; simp
  · simp only [hjl, ite_false]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [ite_eq_right_iff]
    rintro ⟨h1, h2⟩
    exact absurd (h1 ▸ h2) hjl

/-- `E (Σ_k g_k^2)^2 = 3n + n(n-1) = n(n+2)`, with integrability. -/
theorem integral_sum_sq_sq (n : ℕ) :
    Integrable (fun x : Fin n → ℝ => (∑ j, x j ^ 2) ^ 2) (stdPi n) ∧
      ∫ x, (∑ j, x j ^ 2) ^ 2 ∂stdPi n = n * (n + 2) := by
  have hexp : ∀ x : Fin n → ℝ, (∑ j, x j ^ 2) ^ 2 = ∑ j, ∑ l, x j ^ 2 * x l ^ 2 := by
    intro x; rw [sq, Finset.sum_mul_sum]
  simp only [hexp]
  refine ⟨integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    (integral_sq_mul_sq j l).1, ?_⟩
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    (integral_sq_mul_sq j l).1]
  simp only [fun j => integral_finsetSum (μ := stdPi n) (s := Finset.univ)
    (f := fun l x => x j ^ 2 * x l ^ 2) fun l _ => (integral_sq_mul_sq j l).1]
  simp only [fun j l => (integral_sq_mul_sq (n := n) j l).2]
  have hrow : ∀ j : Fin n, ∑ l : Fin n, (if j = l then (3 : ℝ) else 1) = n + 2 := by
    intro j
    have : ∀ l : Fin n, (if j = l then (3 : ℝ) else 1) = 1 + if j = l then 2 else 0 := by
      intro l; split_ifs <;> norm_num
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `V_out = n` (TeX line 187). -/
theorem vOut_rowFamily (n : ℕ) : vOut (rowFamily n) = of fun _ _ => (n : ℂ) := by
  ext a b
  simp [vOut, rowFamily, Matrix.sum_apply, mul_apply]

/-- `V_in = I_n` (TeX line 187). -/
theorem vIn_rowFamily (n : ℕ) : vIn (rowFamily n) = 1 := by
  ext i j
  simp [vIn, rowFamily, Matrix.sum_apply, mul_apply, one_apply, eq_comm]

/-- `V_out = I_n` for the transposed family. -/
theorem vOut_colFamily (n : ℕ) : vOut (colFamily n) = 1 := by
  ext i j
  simp [vOut, colFamily, Matrix.sum_apply, mul_apply, one_apply, eq_comm]

/-- `V_in = n` for the transposed family. -/
theorem vIn_colFamily (n : ℕ) : vIn (colFamily n) = of fun _ _ => (n : ℂ) := by
  ext a b
  simp [vIn, colFamily, Matrix.sum_apply, mul_apply]

end OneVariance

/-! ### The remark's numbers and the probability-space wrappers -/

section Paper

/-- `(x^{1/4})^4 = x` for `x ≥ 0` (exponent written as `1/(2m)`, `m = 2`). -/
theorem rpow_quarter_pow (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / (2 * ((2 : ℕ) : ℝ)))) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `(√3 · y)^4 = 9 y^4` with `√3 = √(2m-1)`, `m = 2`. -/
theorem sqrt_three_mul_pow (y : ℝ) : (√(2 * ((2 : ℕ) : ℝ) - 1) * y) ^ 4 = 9 * y ^ 4 := by
  rw [mul_pow]
  have h : (√(2 * ((2 : ℕ) : ℝ) - 1)) ^ 4 = 9 := by
    have h3 : (√(2 * ((2 : ℕ) : ℝ) - 1)) ^ 2 = 3 := by
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    calc (√(2 * ((2 : ℕ) : ℝ) - 1)) ^ 4 = ((√(2 * ((2 : ℕ) : ℝ) - 1)) ^ 2) ^ 2 := by ring
      _ = 9 := by rw [h3]; norm_num
  rw [h]

/-- `Tr V_in^2 = Tr I_16 = 16` (TeX line 189). -/
theorem trace_vIn_rowFamily_sq : (trace (vIn (rowFamily 16) ^ 2)).re = 16 := by
  simp [vIn_rowFamily]

/-- `Tr V_out^2 = 16^2 = 256`. -/
theorem trace_vOut_rowFamily_sq : (trace (vOut (rowFamily 16) ^ 2)).re = 256 := by
  rw [vOut_rowFamily]
  have : (of fun _ _ => ((16 : ℕ) : ℂ) : Matrix (Fin 1) (Fin 1) ℂ) =
      of fun _ _ => ((16 : ℝ) : ℂ) := by ext; simp
  rw [this, one_by_one_sq]; norm_num

/-- `E ‖X‖_{S_4}^4 = 288` for `n = 16` (TeX line 185), with integrability. -/
theorem integral_schattenPow_rowFamily :
    Integrable (fun x => schattenPow (gaussLin (rowFamily 16) x) 2) (stdPi 16) ∧
      ∫ x, schattenPow (gaussLin (rowFamily 16) x) 2 ∂stdPi 16 = 288 := by
  simp only [schattenPow_rowFamily]
  obtain ⟨h1, h2⟩ := integral_sum_sq_sq 16
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- `E ‖X‖_{S_4}^4 = 288` for the transposed family, with integrability. -/
theorem integral_schattenPow_colFamily :
    Integrable (fun x => schattenPow (gaussLin (colFamily 16) x) 2) (stdPi 16) ∧
      ∫ x, schattenPow (gaussLin (colFamily 16) x) 2 ∂stdPi 16 = 288 := by
  simp only [schattenPow_colFamily]
  obtain ⟨h1, h2⟩ := integral_sum_sq_sq 16
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- `R:gaussian-one-variance-test` (TeX lines 179--193) on `stdPi 16`: for
`n = 16` and the coordinate rows `A_k = e_k^T`, `X X^* = Σ_k g_k^2`,
`E ‖X‖_{S_4}^4 = n(n+2) = 288`, `V_out = n`, `V_in = I_n`; the input-only
form of `E:finite-gaussian-maximum` (fourth power `9 Tr I_n^2 = 144`) is
false; the average and maximum bounds have fourth powers `1224` and `2304`;
for the transposed family `E ‖X‖_{S_4}^4 = 288` again and the output-only
bound (fourth power `144`) is false. -/
theorem gaussian_one_variance_test :
    (∀ x : Fin 16 → ℝ, gaussLin (rowFamily 16) x * (gaussLin (rowFamily 16) x)ᴴ =
      of fun _ _ => ((∑ j, x j ^ 2 : ℝ) : ℂ)) ∧
    Integrable (fun x => schattenPow (gaussLin (rowFamily 16) x) 2) (stdPi 16) ∧
    ∫ x, schattenPow (gaussLin (rowFamily 16) x) 2 ∂stdPi 16 = 288 ∧
    vOut (rowFamily 16) = (of fun _ _ => (16 : ℂ)) ∧ vIn (rowFamily 16) = 1 ∧
    (√(2 * ((2 : ℕ) : ℝ) - 1) * schattenNorm (CFC.sqrt (vIn (rowFamily 16))) 2) ^ 4 = 144 ∧
    ¬ ((∫ x, schattenPow (gaussLin (rowFamily 16) x) 2 ∂stdPi 16) ^ (1 / (2 * ((2 : ℕ) : ℝ))) ≤
        √(2 * ((2 : ℕ) : ℝ) - 1) * schattenNorm (CFC.sqrt (vIn (rowFamily 16))) 2) ∧
    (√(2 * ((2 : ℕ) : ℝ) - 1) * (((trace (vOut (rowFamily 16) ^ 2)).re +
        (trace (vIn (rowFamily 16) ^ 2)).re) / 2) ^ (1 / (2 * ((2 : ℕ) : ℝ)))) ^ 4 = 1224 ∧
    (√(2 * ((2 : ℕ) : ℝ) - 1) * max (schattenNorm (CFC.sqrt (vOut (rowFamily 16))) 2)
        (schattenNorm (CFC.sqrt (vIn (rowFamily 16))) 2)) ^ 4 = 2304 ∧
    ∫ x, schattenPow (gaussLin (colFamily 16) x) 2 ∂stdPi 16 = 288 ∧
    ¬ ((∫ x, schattenPow (gaussLin (colFamily 16) x) 2 ∂stdPi 16) ^ (1 / (2 * ((2 : ℕ) : ℝ))) ≤
        √(2 * ((2 : ℕ) : ℝ) - 1) * schattenNorm (CFC.sqrt (vOut (colFamily 16))) 2) := by
  obtain ⟨hint, hE⟩ := integral_schattenPow_rowFamily
  obtain ⟨-, hE'⟩ := integral_schattenPow_colFamily
  have hIn : schattenNorm (CFC.sqrt (vIn (rowFamily 16))) 2 =
      (16 : ℝ) ^ (1 / (2 * ((2 : ℕ) : ℝ))) := by
    rw [schattenNorm_sqrt (vIn_posSemidef _), trace_vIn_rowFamily_sq]
  have hOut : schattenNorm (CFC.sqrt (vOut (rowFamily 16))) 2 =
      (256 : ℝ) ^ (1 / (2 * ((2 : ℕ) : ℝ))) := by
    rw [schattenNorm_sqrt (vOut_posSemidef _), trace_vOut_rowFamily_sq]
  have hOut' : schattenNorm (CFC.sqrt (vOut (colFamily 16))) 2 =
      (16 : ℝ) ^ (1 / (2 * ((2 : ℕ) : ℝ))) := by
    rw [schattenNorm_sqrt (vOut_posSemidef _), vOut_colFamily]; simp
  have h144 : (√(2 * ((2 : ℕ) : ℝ) - 1) * (16 : ℝ) ^ (1 / (2 * ((2 : ℕ) : ℝ)))) ^ 4 = 144 := by
    rw [sqrt_three_mul_pow, rpow_quarter_pow _ (by norm_num)]; norm_num
  have hneg : ∀ E : ℝ, E = 288 → ¬ (E ^ (1 / (2 * ((2 : ℕ) : ℝ))) ≤
      √(2 * ((2 : ℕ) : ℝ) - 1) * (16 : ℝ) ^ (1 / (2 * ((2 : ℕ) : ℝ)))) := by
    intro E hE h
    have h4 := pow_le_pow_left₀ (Real.rpow_nonneg (by rw [hE]; norm_num) _) h 4
    rw [rpow_quarter_pow _ (by rw [hE]; norm_num), h144, hE] at h4
    norm_num at h4
  refine ⟨rowFamily_mul_conj, hint, hE, by rw [vOut_rowFamily]; simp, vIn_rowFamily 16,
    by rw [hIn, h144], by rw [hIn]; exact hneg _ hE, ?_, ?_, hE',
    by rw [hOut']; exact hneg _ hE'⟩
  · rw [trace_vOut_rowFamily_sq, trace_vIn_rowFamily_sq, sqrt_three_mul_pow,
      rpow_quarter_pow _ (by norm_num)]; norm_num
  · rw [hOut, hIn, max_eq_left (Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)),
      sqrt_three_mul_pow, rpow_quarter_pow _ (by norm_num)]; norm_num

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Continuity of `g ↦ ‖X(g)‖_{S_p}^p` (auxiliary to the Lean proof route). -/
theorem continuous_schattenPow_gaussLin {o n : Type*} [Fintype o] [Fintype n]
    [DecidableEq n] {N : ℕ} (A : Fin N → Matrix o n ℂ) (m : ℕ) :
    Continuous fun x : Fin N → ℝ => schattenPow (gaussLin A x) m := by
  unfold schattenPow gaussLin
  fun_prop

/-- `E:finite-hermitian-gaussian` on a probability space carrying independent
standard Gaussians `g_1, …, g_N` (TeX lines 121--154): for Hermitian `B_k`,
`Y = Σ g_k B_k`, `D = Σ B_k^2`, `m ≥ 1`: `E Tr Y^(2m) ≤ (2m-1)^m Tr D^m`,
with equality `E Tr Y^2 = Tr D` at `m = 1`. -/
theorem finite_hermitian_gaussian_paper {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ}
    (Bs : Fin N → Matrix n n ℂ) (hB : ∀ k, (Bs k).IsHermitian)
    (g : Fin N → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ k, HasLaw (g k) (gaussianReal 0 1) P) (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun ω => (trace (gaussLin Bs (fun k => g k ω) ^ (2 * m))).re) P ∧
      ∫ ω, (trace (gaussLin Bs (fun k => g k ω) ^ (2 * m))).re ∂P ≤
        (2 * (m : ℝ) - 1) ^ m * (trace ((∑ k, Bs k ^ 2) ^ m)).re ∧
      (m = 1 → ∫ ω, (trace (gaussLin Bs (fun k => g k ω) ^ (2 * m))).re ∂P =
        (trace (∑ k, Bs k ^ 2)).re) := by
  have hc : Continuous fun x => (trace (gaussLin Bs x ^ (2 * m))).re := by
    simpa only [Matrix.one_mul, Matrix.mul_one, pow_zero] using continuous_word Bs 1 1 (2 * m) 0
  have hI := integral_comp_eq_stdPi g hind hlaw hc.aestronglyMeasurable
  obtain ⟨h1, h2⟩ := finite_hermitian_gaussian Bs hB m hm
  refine ⟨(integrable_comp_iff_stdPi g hind hlaw hc.aestronglyMeasurable).2 h1,
    by rw [hI]; exact h2, fun h => ?_⟩
  subst h
  rw [hI]; exact integral_trace_sq_eq Bs

/-- `P:finite-gaussian-matrix` (TeX lines 98--118), with the manuscript's
hypotheses: complex `o × n` matrices `A_1, …, A_N` with `o, n, N ≥ 1`,
independent real standard Gaussians `g_k` on a probability space, `X = Σ g_k A_k`,
even `p = 2m ≥ 2`, `‖A‖_{S_p}^p = Tr((A^*A)^m)`.  Conclusions: integrability of
`‖X‖_{S_p}^p`; `(E‖X‖_{S_p}^p)^{1/p} ≤ √(p-1) ((Tr V_out^m + Tr V_in^m)/2)^{1/p}
≤ √(p-1) max(‖V_out^{1/2}‖_{S_p}, ‖V_in^{1/2}‖_{S_p})`; equality in the first
inequality at `p = 2`, where `E‖X‖_{S_2}^2 = Tr V_in = Tr V_out`; and the zero
identity for a zero family.  The constants do not depend on `o, n, N`.  The
hypotheses `o, n, N ≥ 1` are carried but not used (the general theorem
`finite_gaussian_matrix` also covers empty families). -/
theorem finite_gaussian_matrix_paper {o n : Type*} [Fintype o] [Fintype n] [DecidableEq o]
    [DecidableEq n] [Nonempty o] [Nonempty n] {N : ℕ} (_hN : 1 ≤ N)
    (A : Fin N → Matrix o n ℂ) (g : Fin N → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ k, HasLaw (g k) (gaussianReal 0 1) P) (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun ω => schattenPow (gaussLin A (fun k => g k ω)) m) P ∧
      (∫ ω, schattenPow (gaussLin A (fun k => g k ω)) m ∂P) ^ (1 / (2 * (m : ℝ))) ≤
        √(2 * (m : ℝ) - 1) *
          (((trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re) / 2) ^ (1 / (2 * (m : ℝ))) ∧
      √(2 * (m : ℝ) - 1) *
          (((trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re) / 2) ^ (1 / (2 * (m : ℝ))) ≤
        √(2 * (m : ℝ) - 1) *
          max (schattenNorm (CFC.sqrt (vOut A)) m) (schattenNorm (CFC.sqrt (vIn A)) m) ∧
      (m = 1 →
        (∫ ω, schattenPow (gaussLin A (fun k => g k ω)) m ∂P) ^ (1 / (2 * (m : ℝ))) =
          √(2 * (m : ℝ) - 1) *
            (((trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re) / 2) ^ (1 / (2 * (m : ℝ))) ∧
        ∫ ω, schattenPow (gaussLin A (fun k => g k ω)) m ∂P = (trace (vIn A)).re ∧
        (trace (vOut A)).re = (trace (vIn A)).re) ∧
      ((∀ k, A k = 0) →
        ∫ ω, schattenPow (gaussLin A (fun k => g k ω)) m ∂P = 0 ∧
          ((trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re) / 2 = 0 ∧
          schattenNorm (CFC.sqrt (vOut A)) m = 0 ∧
          schattenNorm (CFC.sqrt (vIn A)) m = 0) := by
  have hc := continuous_schattenPow_gaussLin A m
  have hI := integral_comp_eq_stdPi g hind hlaw hc.aestronglyMeasurable
  obtain ⟨h1, h2, h3⟩ := finite_gaussian_matrix A m hm
  refine ⟨(integrable_comp_iff_stdPi g hind hlaw hc.aestronglyMeasurable).2 h1,
    by rw [hI]; exact h2, h3, fun h => ?_, fun h0 => ?_⟩
  · subst h
    obtain ⟨e1, e2, e3⟩ := finite_gaussian_matrix_two A
    exact ⟨by rw [hI]; exact e3, by rw [hI]; exact e1, e2⟩
  · rw [hI]; exact finite_gaussian_matrix_zero A h0 m hm

/-- `R:gaussian-one-variance-test` on a probability space carrying independent
standard Gaussians `g_1, …, g_16`: `E g_k^2 = 1`, `E g_k^4 = 3`,
`E ‖X‖_{S_4}^4 = 288` for `X = Σ g_k e_k^T`, and the input-only bound is false;
for the transposed family the output-only bound is false. -/
theorem gaussian_one_variance_test_paper (g : Fin 16 → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ k, HasLaw (g k) (gaussianReal 0 1) P) :
    (∀ k, ∫ ω, g k ω ^ 2 ∂P = 1 ∧ ∫ ω, g k ω ^ 4 ∂P = 3) ∧
    ∫ ω, schattenPow (gaussLin (rowFamily 16) (fun k => g k ω)) 2 ∂P = 288 ∧
    ¬ ((∫ ω, schattenPow (gaussLin (rowFamily 16) (fun k => g k ω)) 2 ∂P) ^
          (1 / (2 * ((2 : ℕ) : ℝ))) ≤
        √(2 * ((2 : ℕ) : ℝ) - 1) * schattenNorm (CFC.sqrt (vIn (rowFamily 16))) 2) ∧
    ∫ ω, schattenPow (gaussLin (colFamily 16) (fun k => g k ω)) 2 ∂P = 288 ∧
    ¬ ((∫ ω, schattenPow (gaussLin (colFamily 16) (fun k => g k ω)) 2 ∂P) ^
          (1 / (2 * ((2 : ℕ) : ℝ))) ≤
        √(2 * ((2 : ℕ) : ℝ) - 1) * schattenNorm (CFC.sqrt (vOut (colFamily 16))) 2) := by
  obtain ⟨-, -, hE, -, -, -, hn, -, -, hE', hn'⟩ := gaussian_one_variance_test
  have hI := integral_comp_eq_stdPi g hind hlaw
    (continuous_schattenPow_gaussLin (rowFamily 16) 2).aestronglyMeasurable
  have hI' := integral_comp_eq_stdPi g hind hlaw
    (continuous_schattenPow_gaussLin (colFamily 16) 2).aestronglyMeasurable
  have hmom : ∀ k (j : ℕ), ∫ ω, g k ω ^ j ∂P = ∫ x, x ^ j ∂gaussianReal 0 1 := by
    intro k j
    rw [← (hlaw k).map_eq, integral_map (hlaw k).aemeasurable (by fun_prop)]
  refine ⟨fun k => ⟨by rw [hmom, moment_two], by rw [hmom, moment_four]⟩,
    by rw [hI]; exact hE, by rw [hI]; exact hn, by rw [hI']; exact hE', by rw [hI']; exact hn'⟩

end Paper

end StratonovichHAMSecondMoment.FiniteGaussianMatrix
