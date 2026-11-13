module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Consumers of the Hermite/Fock foundation (`GaussianHermite`, `HermiteFock`) in
`notes/notes_stratonovich_ham_second_moment.tex` (main TeX; line numbers at
revision a284420).

Formalized:
* `L:fock-form` (statement lines 2472-2489, `E:fock-sandwich` 2484-2488, proof
  2491-2527): the Fock half of the proof and the compression by `S_b`
  (lines 2511-2513) are proved; the spatial half (lines 2492-2511: Gaussian
  isometry, Plancherel and `E:phase-resolvent` of `L:phase-contractions`, giving
  `∑_i H_i² ≤ R_α ρ^{α-4}`) is the named input `FockColumn`.  Wrapper
  `fock_form_paper`.  Class: inputs supplied.
* `L:interval-contractions` (statement 2828-2848, proof 2850-2897):
  `E:interval-column` (2832-2835) is the named input (`FockColumn` at
  `R_α ρ^{α-2}` for the operators `A_ρ^{-1/2} M_{e_m}`); proved from it: the
  same column bound for band-compressed multiplications (2875-2878), the phase
  insertion on a vacuum color with norm at most `√R_α ρ^{(α-2)/2}`
  (2838-2841, 2878-2880), the substitution `∑ (A^{-1/2} M A^{-1/2})² ≤
  R_α ρ^{α-4}` (2882-2886) and `E:interval-fock` (2844-2846, 2887-2891).
  Wrapper `interval_contractions_paper`.  Class: inputs supplied.
* `E:occupied-multiplication` (lines 1802-1804, inside the proof of
  `P:mild-construction`, statement 1773-1787, proof from line 1793) for finitely many coordinates:
  `‖HF‖₂ ≤ 2√(n+1) ‖H‖₂ ‖F‖₂` for `H = ∑_i a_i g_i` and `F` a real polynomial
  of total degree at most `n` in independent standard Gaussians
  `g_1, …, g_m`, both on `stdPi m` (`occupied_multiplication`) and on a
  probability space (`occupied_multiplication_paper`).  Narrower than the TeX:
  `F` ranges over polynomials in finitely many coordinates and `H` over their
  span, not over the closed space `P_{≤n}` and all centered linear Gaussians;
  the closure step and the almost-sure identification (lines 1810-1814) are not
  formalized.  The spanning step (monomials of degree `≤ n` lie in the Hermite
  span of degree `≤ n`) is `GaussianHermite.mvPolynomial_mem_hermiteSpan`.
* The degree-raising hypothesis of `StratonovichHAMAudit.HermiteWord.cut_eq_raw`
  for a concrete Fock model (`goodDeg_vac`, `goodDeg_insert`, `goodDeg_frame`,
  `truncC_eq`): coefficient vectors over colors `Fin m` (one Gaussian mode per
  color), insertion `J i v = gmul i (K_i v)`, frames acting on `X`, and
  per-color degree truncation `P`.  They have exactly the shapes of the
  hypotheses `hv₀`, `hJ`, `hF`, `hP` of `cut_eq_raw` (with
  `bump i d = fun c => d c + if c = i then 1 else 0`); the application itself
  needs a non-`module` file, since `HermiteWord` is not a `module`.

Model.  Spatial `L²` is an abstract complex inner product space `X`; the
operators of the TeX enter as continuous linear maps on `X`:
`H_i` for `A_ρ^{-1/2} M_{e_i} A_ρ^{-1/2}`, `P` for the band projection `S_b`,
`S` for `A_ρ^{-1/2}`.  The Gaussian factor is `HermiteFock`'s coefficient model
(degrees `≤ N`, truncation `P_N` = restriction of coefficients) or its
expansion `iota` on `stdPi m`.  Self-adjointness is used in the symmetric form
`⟪T u, w⟫ = ⟪u, T w⟫`, derived from `IsSelfAdjoint` in the wrappers.
Route difference: general coefficient operators `H_i` replace the TeX's
rotated basis, and the annihilation part is bounded through the finite
adjoint identity (see `HermiteFock`).

Standing hypotheses in the wrappers: for `L:fock-form`, the class of
`S:static-phase` (lines 2054-2066): `0 < α < 2`, `Γ` even, positive definite,
tempered, locally finite on `ℝ³` with `Γ(rA) = r^{3-α} Γ(A)`, spectral measure
`μ` (locally finite), `R_α = απ μ(B_1)/(2 sin(πα/2))`; for
`L:interval-contractions`, `H:homog` (`HomogCovariance`, as in the other
`S:interval-upper` wrappers) and the same `R_α`.  Of these only `0 < α < 2`
(in the interval wrapper derived from the fields `alpha_range`, `threshold` and
`alpha0_pos` of `HomogCovariance`) and the formula for `R_α` are used (to get
`R_α ≥ 0`); the rest are carried and unused, as is the smoothing width
`ε > 0`.

Junk values: `ρ > 0` throughout, so `ρ^{α-4}`, `ρ^{α-2}`, `ρ^{α/2-2}` are
genuine powers; square roots are of nonnegative reals (`R_α ≥ 0` is proved);
every integral conclusion includes integrability.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.GaussianIBP
public import StratonovichHAMSecondMoment.GaussianHermite
public import StratonovichHAMSecondMoment.HermiteFock
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.IntervalScalar
public import StratonovichHAMSecondMoment.StaticPhaseCauchy

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset Real
open scoped Pointwise
open StratonovichHAMSecondMoment.HermiteFock
open StratonovichHAMSecondMoment.GaussianHermite (hk unitIdx HermiteSpan)

namespace StratonovichHAMSecondMoment.FockForm

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {m : ℕ}

/-! ### The named input and operator facts -/

/-- **Named input `FockColumn`** (the spatial column bound): the family
`H_1, …, H_m` satisfies `∑_i ‖H_i u‖² ≤ c ‖u‖²` for all `u`.  In `L:fock-form`
it stands for `∑_i H_i² ≤ R_α ρ^{α-4}` for `H_i = A_ρ^{-1/2} M_{e_i} A_ρ^{-1/2}`
(main TeX lines 2496-2511: Gaussian isometry, spatial Plancherel and
`E:phase-resolvent` of `L:phase-contractions`); in `L:interval-contractions`
it stands for `E:interval-column` (lines 2832-2835) with the operators
`A_ρ^{-1/2} M_{e_m}` and `c = R_α ρ^{α-2}`.  The manuscript states these for
the full mode family; a finite family is a sub-sum, so the input is no
stronger. -/
def FockColumn (H : Fin m → X →L[ℂ] X) (c : ℝ) : Prop :=
  ∀ u, ∑ i, ‖H i u‖ ^ 2 ≤ c * ‖u‖ ^ 2

/-- A self-adjoint operator is symmetric. -/
theorem symm_of_isSelfAdjoint [CompleteSpace X] {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (u w : X) : inner ℂ (T u) w = inner ℂ u (T w) :=
  hT.isSymmetric u w

/-- A symmetric idempotent (an orthogonal projection, such as the band
projection `S_b`) does not increase norms. -/
theorem norm_proj_le {P : X →L[ℂ] X} (hPs : ∀ u w, inner ℂ (P u) w = inner ℂ u (P w))
    (hPP : ∀ u, P (P u) = P u) (u : X) : ‖P u‖ ≤ ‖u‖ := by
  have h : ‖P u‖ ^ 2 ≤ ‖u‖ * ‖P u‖ := by
    rw [@norm_sq_eq_re_inner ℂ, hPs, hPP]
    exact re_inner_le_norm _ _
  rcases (norm_nonneg (P u)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

/-- Compression preserves symmetry: `P H P` is symmetric for symmetric `P, H`. -/
theorem compress_symm {P T : X →L[ℂ] X} (hPs : ∀ u w, inner ℂ (P u) w = inner ℂ u (P w))
    (hT : ∀ u w, inner ℂ (T u) w = inner ℂ u (T w)) (u w : X) :
    inner ℂ ((P ∘L T ∘L P) u) w = inner ℂ u ((P ∘L T ∘L P) w) := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [hPs, hT, hPs]

/-- **Compression by `S_b`** (main TeX lines 2511-2513): if `∑_i ‖H_i u‖² ≤ c‖u‖²`
with `c ≥ 0` and `P` is a symmetric idempotent, then the same bound holds for
`P H_i P`. -/
theorem fockColumn_compress {H : Fin m → X →L[ℂ] X} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : FockColumn H c) {P : X →L[ℂ] X} (hPs : ∀ u w, inner ℂ (P u) w = inner ℂ u (P w))
    (hPP : ∀ u, P (P u) = P u) : FockColumn (fun i => P ∘L H i ∘L P) c := by
  intro u
  calc ∑ i, ‖(P ∘L H i ∘L P) u‖ ^ 2 ≤ ∑ i, ‖H i (P u)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
          (norm_proj_le hPs hPP _) 2
    _ ≤ c * ‖P u‖ ^ 2 := hc (P u)
    _ ≤ c * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_proj_le hPs hPP u) 2) hc0

/-- Auxiliary: `√(R ρ^{α-4}) = √R ρ^{α/2-2}` for `ρ > 0`, `R ≥ 0`, so the
Fock constant `2√(N+1)√(R ρ^{α-4})` is `d_N ρ^{α/2-2}`. -/
theorem fock_const_eq (N : ℕ) {R ρ alpha : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) :
    2 * √((N : ℝ) + 1) * √(R * ρ ^ (alpha - 4)) =
      StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2) := by
  have h : √(ρ ^ (alpha - 4)) = ρ ^ (alpha / 2 - 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hρ.le]; congr 1; ring
  rw [Real.sqrt_mul hR, h, StaticPhaseCauchy.fockD]; ring

/-! ### `L:fock-form` -/

/-- **`L:fock-form`, general form** (`E:fock-sandwich`, main TeX lines
2484-2488).  Let `H_1, …, H_m` be symmetric operators on `X` with the column
bound `FockColumn H (R ρ^{α-4})` (named input; `R ≥ 0`, `ρ > 0`), and `P` a
symmetric idempotent (the band projection `S_b`).  Then for every `N`, on
coefficient vectors `v` of Hermite degree at most `N`, the operator
`B = P_N (∑_i g_i ⊗ P H_i P) P_N` satisfies
(i) `∑_{|k| ≤ N} ‖(B v)_k‖² ≤ (d_N ρ^{α/2-2})² ∑_{|k| ≤ N} ‖v_k‖²`;
(ii) the same bound in Gaussian `L²(γ_m; X)` for the expansions `iota`, with
integrability; (iii) `B` is symmetric on degrees `≤ N`. -/
theorem fock_form {R ρ alpha : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w))
    (hcol : FockColumn H (R * ρ ^ (alpha - 4))) (P : X →L[ℂ] X)
    (hPs : ∀ u w, inner ℂ (P u) w = inner ℂ u (P w)) (hPP : ∀ u, P (P u) = P u)
    (N : ℕ) {v : (Fin m → ℕ) → X} (hv : Supp N v) :
    ∑ k ∈ degLE m N, ‖fieldOp (fun i => P ∘L H i ∘L P) v k‖ ^ 2 ≤
        (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 * ∑ k ∈ degLE m N, ‖v k‖ ^ 2 ∧
      Integrable (fun x => ‖iota N (fieldOp (fun i => P ∘L H i ∘L P) v) x‖ ^ 2)
        (GaussianIBP.stdPi m) ∧
      ∫ x, ‖iota N (fieldOp (fun i => P ∘L H i ∘L P) v) x‖ ^ 2 ∂GaussianIBP.stdPi m ≤
        (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
          ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m ∧
      ∀ w : (Fin m → ℕ) → X, Supp N w →
        ∑ k ∈ degLE m N, inner ℂ (fieldOp (fun i => P ∘L H i ∘L P) v k) (w k) =
          ∑ k ∈ degLE m N, inner ℂ (v k) (fieldOp (fun i => P ∘L H i ∘L P) w k) := by
  have hc0 : 0 ≤ R * ρ ^ (alpha - 4) := mul_nonneg hR (Real.rpow_nonneg hρ.le _)
  have hsym : ∀ i u w, inner ℂ ((P ∘L H i ∘L P) u) w = inner ℂ u ((P ∘L H i ∘L P) w) :=
    fun i => compress_symm hPs (hH i)
  have hcomp := fockColumn_compress hc0 hcol hPs hPP
  have hconst := fock_const_eq N (alpha := alpha) hR hρ
  obtain ⟨hint, hb⟩ := gaussian_field_bound_trunc N _ hsym hc0 hcomp hv
  refine ⟨?_, hint, ?_, fun w hw => fieldOp_symm_trunc N _ hsym hv hw⟩
  · rw [← hconst]; exact fieldOp_bound_trunc N _ hsym hc0 hcomp hv
  · rw [← hconst]; exact hb

/-- **`L:fock-form`** (main TeX lines 2472-2489, proof 2491-2527) with the
manuscript's hypotheses: the class of `S:static-phase` (lines 2054-2066) on
`ℝ³` (`0 < α < 2`; `Γ` even, positive definite, tempered, locally finite, with
`Γ(rA) = r^{3-α}Γ(A)`; `μ` locally finite with `Γ = ∫ e^{iξ·x} μ(dξ)`),
`R = R_α = απ μ(B_1)/(2 sin(πα/2))`, `ε > 0`, `ρ > 0`, a finite mode number
`m`, a band projection `P = S_b` (symmetric idempotent), and the self-adjoint
spatial sandwiches `H_i = A_ρ^{-1/2} M_{e_i} A_ρ^{-1/2}` with the supplied
column bound `FockColumn H (R_α ρ^{α-4})` (named input, lines 2496-2511).
Conclusion: for every `N`, `B_{N,m,b}` sandwiched by `A_ρ^{-1/2}` (which is
`P_N (∑_i g_i ⊗ S_b H_i S_b) P_N`, since `S_b` commutes with `A_ρ`) is
symmetric and has norm at most `d_N ρ^{α/2-2}`, `d_N = 2√(N+1)√R_α`, on the
coefficient model and in Gaussian `L²`.  Inputs supplied: the spatial half
(`hcol`), self-adjointness of the `H_i` (`hH`, line 2495) and the
identification of the abstract operators with the TeX's spatial operators.
Used: `0 < α < 2` and `hRdef` (for `R_α ≥ 0`), `ρ > 0`; carried and unused:
`_hΓ`, `_hμ`, `_hΓe`, `_hΓt`, `_hΓp`, `_hspec`, `_hscal`, `_hε`. -/
theorem fock_form_paper [CompleteSpace X] {alpha R ε ρ : ℝ}
    (Γ μ : Measure (HomogHypothesis.Rd 3))
    (_hΓ : IsLocallyFiniteMeasure Γ) (_hμ : IsLocallyFiniteMeasure μ)
    (_hΓe : HomogHypothesis.IsEven Γ) (_hΓt : HomogHypothesis.IsTempered Γ)
    (_hΓp : HomogHypothesis.IsPosDefDistr Γ) (_hspec : HomogHypothesis.IsSpectralMeasure Γ μ)
    (_hscal : ∀ A : Set (HomogHypothesis.Rd 3), MeasurableSet A → ∀ c : ℝ, 0 < c →
      Γ (c • A) = ENNReal.ofReal (c ^ ((3 : ℝ) - alpha)) * Γ A)
    (hα0 : 0 < alpha) (hα2 : alpha < 2)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (_hε : 0 < ε) (hρ : 0 < ρ)
    (H : Fin m → X →L[ℂ] X) (hH : ∀ i, IsSelfAdjoint (H i))
    (hcol : FockColumn H (R * ρ ^ (alpha - 4)))
    (P : X →L[ℂ] X) (hP : IsSelfAdjoint P) (hPP : P ∘L P = P)
    (N : ℕ) {v : (Fin m → ℕ) → X} (hv : Supp N v) :
    ∑ k ∈ degLE m N, ‖fieldOp (fun i => P ∘L H i ∘L P) v k‖ ^ 2 ≤
        (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 * ∑ k ∈ degLE m N, ‖v k‖ ^ 2 ∧
      Integrable (fun x => ‖iota N (fieldOp (fun i => P ∘L H i ∘L P) v) x‖ ^ 2)
        (GaussianIBP.stdPi m) ∧
      ∫ x, ‖iota N (fieldOp (fun i => P ∘L H i ∘L P) v) x‖ ^ 2 ∂GaussianIBP.stdPi m ≤
        (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
          ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m ∧
      ∀ w : (Fin m → ℕ) → X, Supp N w →
        ∑ k ∈ degLE m N, inner ℂ (fieldOp (fun i => P ∘L H i ∘L P) v k) (w k) =
          ∑ k ∈ degLE m N, inner ℂ (v k) (fieldOp (fun i => P ∘L H i ∘L P) w k) :=
  fock_form (hRdef ▸ IntervalScalar.ralpha_nonneg μ hα0 hα2) hρ H
    (fun i => symm_of_isSelfAdjoint (hH i)) hcol P (symm_of_isSelfAdjoint hP)
    (fun u => by rw [← ContinuousLinearMap.comp_apply, hPP]) N hv

/-! ### `L:interval-contractions` -/

/-- **`L:interval-contractions`, general form** (main TeX lines 2828-2897).
Let `S` (standing for `A_ρ^{-1/2}`) be symmetric with `‖S f‖ ≤ ρ^{-1}‖f‖`, let
`M_1, …, M_m` (the multiplications `M_{e_m}`) be symmetric, and let `P` (a band
projection `S_b`) be a symmetric idempotent commuting with `S`.  Assume
`E:interval-column` as the named input `FockColumn (S M) (R ρ^{α-2})`,
`R ≥ 0`, `ρ > 0`.  Then:
(a) the column bound holds for the band-compressed `S P M_i P` (lines
2875-2878);
(b) phase insertion on a vacuum color: for `u, w ∈ X`,
`∫ ‖∑_i x_i S P M_i P u‖² dγ_m = ∑_i ‖S P M_i P u‖² ≤ R ρ^{α-2}(‖u‖² + ‖S w‖²)`,
the squared form of the norm bound `√R ρ^{(α-2)/2}` for
`(u, w) ↦ (0, W u)` in `‖(f,g)‖_ρ² = ‖f‖² + ‖A_ρ^{-1/2} g‖²` (lines
2838-2841, 2878-2880), with integrability;
(c) `H_i = S P M_i P S` is symmetric with column bound `R ρ^{α-4}` (lines
2882-2886);
(d) `E:interval-fock`: on degrees `≤ N` the truncated sandwiched field has
norm at most `d_N ρ^{α/2-2}`, on the coefficient model and in Gaussian `L²`. -/
theorem interval_contractions {R ρ alpha : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ)
    (S : X →L[ℂ] X) (hSs : ∀ u w, inner ℂ (S u) w = inner ℂ u (S w))
    (hSn : ∀ f, ‖S f‖ ≤ ρ⁻¹ * ‖f‖)
    (M : Fin m → X →L[ℂ] X) (hM : ∀ i u w, inner ℂ (M i u) w = inner ℂ u (M i w))
    (hcol : FockColumn (fun i => S ∘L M i) (R * ρ ^ (alpha - 2)))
    (P : X →L[ℂ] X) (hPs : ∀ u w, inner ℂ (P u) w = inner ℂ u (P w))
    (hPP : ∀ u, P (P u) = P u) (hPS : ∀ u, P (S u) = S (P u)) :
    FockColumn (fun i => S ∘L (P ∘L M i ∘L P)) (R * ρ ^ (alpha - 2)) ∧
      (∀ u w : X,
        Integrable (fun x => ‖∑ i, ((x i : ℝ) : ℂ) • (S ∘L (P ∘L M i ∘L P)) u‖ ^ 2)
          (GaussianIBP.stdPi m) ∧
        ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • (S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ∂GaussianIBP.stdPi m =
          ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ∧
        ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ≤ R * ρ ^ (alpha - 2) * (‖u‖ ^ 2 + ‖S w‖ ^ 2)) ∧
      (∀ i u w, inner ℂ ((S ∘L (P ∘L M i ∘L P) ∘L S) u) w =
        inner ℂ u ((S ∘L (P ∘L M i ∘L P) ∘L S) w)) ∧
      FockColumn (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) (R * ρ ^ (alpha - 4)) ∧
      ∀ (N : ℕ) (v : (Fin m → ℕ) → X), Supp N v →
        ∑ k ∈ degLE m N, ‖fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v k‖ ^ 2 ≤
          (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
            ∑ k ∈ degLE m N, ‖v k‖ ^ 2 ∧
        Integrable (fun x => ‖iota N (fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v) x‖ ^ 2)
          (GaussianIBP.stdPi m) ∧
        ∫ x, ‖iota N (fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v) x‖ ^ 2
            ∂GaussianIBP.stdPi m ≤
          (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
            ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m := by
  have hc0 : 0 ≤ R * ρ ^ (alpha - 2) := mul_nonneg hR (Real.rpow_nonneg hρ.le _)
  -- (a) band compression
  have ha : FockColumn (fun i => S ∘L (P ∘L M i ∘L P)) (R * ρ ^ (alpha - 2)) := by
    intro u
    calc ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ≤ ∑ i, ‖(S ∘L M i) (P u)‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          simp only [ContinuousLinearMap.comp_apply]
          rw [← hPS]; exact norm_proj_le hPs hPP _
      _ ≤ R * ρ ^ (alpha - 2) * ‖P u‖ ^ 2 := hcol (P u)
      _ ≤ R * ρ ^ (alpha - 2) * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_proj_le hPs hPP u) 2) hc0
  -- (c) substitution
  have hsym : ∀ i u w, inner ℂ ((S ∘L (P ∘L M i ∘L P) ∘L S) u) w =
      inner ℂ u ((S ∘L (P ∘L M i ∘L P) ∘L S) w) := by
    intro i u w
    simp only [ContinuousLinearMap.comp_apply]
    rw [hSs, hPs, hM, hPs, hSs]
  have hρ2 : ρ ^ (alpha - 2) * ρ⁻¹ ^ 2 = ρ ^ (alpha - 4) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
    congr 1; push_cast; ring
  have hc : FockColumn (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) (R * ρ ^ (alpha - 4)) := by
    intro u
    calc ∑ i, ‖(S ∘L (P ∘L M i ∘L P) ∘L S) u‖ ^ 2 = ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) (S u)‖ ^ 2 :=
          rfl
      _ ≤ R * ρ ^ (alpha - 2) * ‖S u‖ ^ 2 := ha (S u)
      _ ≤ R * ρ ^ (alpha - 2) * (ρ⁻¹ * ‖u‖) ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hSn u) 2) hc0
      _ = R * ρ ^ (alpha - 4) * ‖u‖ ^ 2 := by rw [← hρ2]; ring
  have hc0' : 0 ≤ R * ρ ^ (alpha - 4) := mul_nonneg hR (Real.rpow_nonneg hρ.le _)
  have hconst : ∀ N : ℕ, 2 * √((N : ℝ) + 1) * √(R * ρ ^ (alpha - 4)) =
      StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2) := fun N => fock_const_eq N hR hρ
  refine ⟨ha, fun u w => ?_, hsym, hc, fun N v hv => ?_⟩
  · obtain ⟨h1, h2⟩ := vacuum_insertion_isometry (fun i => (S ∘L (P ∘L M i ∘L P)) u)
    refine ⟨h1, h2, (ha u).trans (mul_le_mul_of_nonneg_left ?_ hc0)⟩
    nlinarith [sq_nonneg ‖S w‖]
  · obtain ⟨hint, hb⟩ := gaussian_field_bound_trunc N _ hsym hc0' hc hv
    refine ⟨?_, hint, ?_⟩
    · rw [← hconst]; exact fieldOp_bound_trunc N _ hsym hc0' hc hv
    · rw [← hconst]; exact hb

/-- **`L:interval-contractions`** (main TeX lines 2828-2848, proof 2850-2897)
with the manuscript's hypotheses: `H:homog` (`HomogCovariance d α α₀ Γ μ`, the
standing class of `S:interval-upper`, lines 2803-2824), `R = R_α`, `ε > 0`,
`ρ > 0`, finite mode number `m`, `A_ρ^{-1/2}` as a self-adjoint `S` with
`‖S f‖ ≤ ρ^{-1}‖f‖` (`A_ρ ≥ ρ²`), self-adjoint multiplications `M_i`, a
band projection `P` (self-adjoint idempotent) commuting with `S`, and
`E:interval-column` as the supplied input `hcol`.  Conclusions (a)-(d) of
`interval_contractions`: the band-compressed column bound, the vacuum phase
insertion, the substituted column bound `R_α ρ^{α-4}` with symmetry, and
`E:interval-fock` (`d_N ρ^{α/2-2}`).  Inputs supplied: `hcol`
(`E:interval-column`), `hSn` (the norm of `A_ρ^{-1/2}`), self-adjointness and
the identification of the abstract operators with the TeX's.  "Tensoring with
any other Hilbert factor" is the arbitrary `X`.  Used from `H:homog`: the
fields `alpha_range`, `threshold`, `alpha0_pos` (for `0 < α < 2`, hence
`R_α ≥ 0`); the other fields of `hH` and `_hε` are carried and unused. -/
theorem interval_contractions_paper [CompleteSpace X] {d : ℕ} {alpha alpha0 R ε ρ : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (_hε : 0 < ε) (hρ : 0 < ρ)
    (S : X →L[ℂ] X) (hS : IsSelfAdjoint S) (hSn : ∀ f, ‖S f‖ ≤ ρ⁻¹ * ‖f‖)
    (M : Fin m → X →L[ℂ] X) (hM : ∀ i, IsSelfAdjoint (M i))
    (hcol : FockColumn (fun i => S ∘L M i) (R * ρ ^ (alpha - 2)))
    (P : X →L[ℂ] X) (hP : IsSelfAdjoint P) (hPP : P ∘L P = P) (hPS : P ∘L S = S ∘L P) :
    FockColumn (fun i => S ∘L (P ∘L M i ∘L P)) (R * ρ ^ (alpha - 2)) ∧
      (∀ u w : X,
        Integrable (fun x => ‖∑ i, ((x i : ℝ) : ℂ) • (S ∘L (P ∘L M i ∘L P)) u‖ ^ 2)
          (GaussianIBP.stdPi m) ∧
        ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • (S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ∂GaussianIBP.stdPi m =
          ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ∧
        ∑ i, ‖(S ∘L (P ∘L M i ∘L P)) u‖ ^ 2 ≤ R * ρ ^ (alpha - 2) * (‖u‖ ^ 2 + ‖S w‖ ^ 2)) ∧
      (∀ i, IsSelfAdjoint (S ∘L (P ∘L M i ∘L P) ∘L S)) ∧
      FockColumn (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) (R * ρ ^ (alpha - 4)) ∧
      ∀ (N : ℕ) (v : (Fin m → ℕ) → X), Supp N v →
        ∑ k ∈ degLE m N, ‖fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v k‖ ^ 2 ≤
          (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
            ∑ k ∈ degLE m N, ‖v k‖ ^ 2 ∧
        Integrable (fun x => ‖iota N (fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v) x‖ ^ 2)
          (GaussianIBP.stdPi m) ∧
        ∫ x, ‖iota N (fieldOp (fun i => S ∘L (P ∘L M i ∘L P) ∘L S) v) x‖ ^ 2
            ∂GaussianIBP.stdPi m ≤
          (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
            ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m := by
  have hα0 : 0 < alpha := by
    rcases hH.alpha_range with h | h
    · exact h.1
    · rw [h.1]; rcases h.2 with rfl; norm_num
  have hα2 : alpha < 2 := by linarith [hH.threshold, hH.alpha0_pos]
  have hR := hRdef ▸ IntervalScalar.ralpha_nonneg μ hα0 hα2
  obtain ⟨ha, hb, hsym, hc, hd⟩ := interval_contractions hR hρ S (symm_of_isSelfAdjoint hS) hSn
    M (fun i => symm_of_isSelfAdjoint (hM i)) hcol P (symm_of_isSelfAdjoint hP)
    (fun u => by rw [← ContinuousLinearMap.comp_apply, hPP])
    (fun u => by rw [← ContinuousLinearMap.comp_apply, hPS, ContinuousLinearMap.comp_apply])
  refine ⟨ha, hb, fun i => ?_, hc, hd⟩
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact hsym i

/-! ### `E:occupied-multiplication` for finitely many coordinates -/

/-- **`E:occupied-multiplication`, finite coordinates** (main TeX lines
1802-1804, proof 1805-1810), on `stdPi m`: for `H(x) = ∑_i a_i x_i` and
`F(x) = p(x)` with `p` a real polynomial of total degree at most `n`,
`E[(HF)²] ≤ 4(n+1) E[H²] E[F²]`, all three integrands integrable.  (This is
`‖HF‖₂ ≤ 2√(n+1)‖H‖₂‖F‖₂` squared.)  Proof: the spanning step
`mvPolynomial_mem_hermiteSpan`, then `gaussian_field_bound` with `X = ℂ`,
`H_i = a_i` (column constant `∑_i a_i² = E[H²]`). -/
theorem occupied_multiplication (n : ℕ) (a : Fin m → ℝ) (p : MvPolynomial (Fin m) ℝ)
    (hp : p.totalDegree ≤ n) :
    Integrable (fun x => ((∑ i, a i * x i) * MvPolynomial.eval x p) ^ 2) (GaussianIBP.stdPi m) ∧
      Integrable (fun x => (∑ i, a i * x i) ^ 2) (GaussianIBP.stdPi m) ∧
      Integrable (fun x => (MvPolynomial.eval x p) ^ 2) (GaussianIBP.stdPi m) ∧
      ∫ x, ((∑ i, a i * x i) * MvPolynomial.eval x p) ^ 2 ∂GaussianIBP.stdPi m ≤
        4 * ((n : ℝ) + 1) * (∫ x, (∑ i, a i * x i) ^ 2 ∂GaussianIBP.stdPi m) *
          ∫ x, (MvPolynomial.eval x p) ^ 2 ∂GaussianIBP.stdPi m := by
  classical
  obtain ⟨c, hc⟩ := GaussianHermite.mvPolynomial_mem_hermiteSpan n p hp
  simp only at hc
  set v : (Fin m → ℕ) → ℂ := fun k => if k ∈ degLE m n then ((c k : ℝ) : ℂ) else 0
  have hv : Supp n v := fun k hk => by
    have : k ∉ degLE m n := by rw [mem_degLE]; omega
    simp only [v, this, ↓reduceIte]
  have hF : ∀ x, iota n v x = ((MvPolynomial.eval x p : ℝ) : ℂ) := by
    intro x
    rw [hc x, iota]; push_cast
    exact Finset.sum_congr rfl fun k hk => by
      have hk' : k ∈ degLE m n := hk
      simp only [v, hk', ↓reduceIte, smul_eq_mul]; ring
  set A : Fin m → ℂ →L[ℂ] ℂ := fun i => ((a i : ℝ) : ℂ) • ContinuousLinearMap.id ℂ ℂ
  have hAs : ∀ i u w, inner ℂ (A i u) w = inner ℂ u (A i w) := by
    intro i u w
    simp [A]; ring
  have hc0 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAc : ∀ u, ∑ i, ‖A i u‖ ^ 2 ≤ (∑ i, a i ^ 2) * ‖u‖ ^ 2 := by
    intro u
    simp [A, mul_pow, Finset.sum_mul]
  obtain ⟨h1, h2, h3⟩ := gaussian_field_bound n A hAs hc0 hAc hv
  have hHF : ∀ x, ‖∑ i, ((x i : ℝ) : ℂ) • A i (iota n v x)‖ ^ 2 =
      ((∑ i, a i * x i) * MvPolynomial.eval x p) ^ 2 := by
    intro x
    rw [hF x]
    simp only [A, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    have e : ∑ i, ((x i : ℝ) : ℂ) * (((a i : ℝ) : ℂ) * ((MvPolynomial.eval x p : ℝ) : ℂ)) =
        (((∑ i, a i * x i) * MvPolynomial.eval x p : ℝ) : ℂ) := by
      push_cast; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hFF : ∀ x, ‖iota n v x‖ ^ 2 = (MvPolynomial.eval x p) ^ 2 := by
    intro x; rw [hF x, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  obtain ⟨h4, h5⟩ := vacuum_insertion_isometry (m := m) (fun i => ((a i : ℝ) : ℂ))
  have hHH : ∀ x : Fin m → ℝ, ‖∑ i, ((x i : ℝ) : ℂ) • ((a i : ℝ) : ℂ)‖ ^ 2 =
      (∑ i, a i * x i) ^ 2 := by
    intro x
    rw [show ∑ i, ((x i : ℝ) : ℂ) • ((a i : ℝ) : ℂ) = ((∑ i, a i * x i : ℝ) : ℂ) by
      push_cast; exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨h1.congr (ae_of_all _ hHF), h4.congr (ae_of_all _ hHH), h2.congr (ae_of_all _ hFF), ?_⟩
  have hsq : (2 * √((n : ℝ) + 1) * √(∑ i, a i ^ 2)) ^ 2 = 4 * ((n : ℝ) + 1) * ∑ i, a i ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hc0]; ring
  have hH2 : ∫ x, (∑ i, a i * x i) ^ 2 ∂GaussianIBP.stdPi m = ∑ i, a i ^ 2 := by
    rw [← integral_congr_ae (ae_of_all _ hHH), h5]
    simp [Complex.norm_real]
  calc ∫ x, ((∑ i, a i * x i) * MvPolynomial.eval x p) ^ 2 ∂GaussianIBP.stdPi m
      = ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • A i (iota n v x)‖ ^ 2 ∂GaussianIBP.stdPi m :=
        (integral_congr_ae (ae_of_all _ hHF)).symm
    _ ≤ _ := h3
    _ = _ := by rw [integral_congr_ae (ae_of_all _ hFF), hsq, hH2]

/-- **`E:occupied-multiplication`** (main TeX lines 1802-1804, inside the proof
of `P:mild-construction`, which starts at line 1793), for finitely many coordinates, on a
probability space: for independent standard Gaussians `g_1, …, g_m`, the
centered linear Gaussian `H = ∑_i a_i g_i` and `F = p(g_1, …, g_m)` with `p` a
real polynomial of total degree at most `n`,
`‖HF‖₂ ≤ 2√(n+1) ‖H‖₂ ‖F‖₂`, with `HF`, `H`, `F` square integrable.
Narrower than the TeX (stated in the module doc): `F` is a polynomial in
finitely many coordinates and `H` lies in their span; the closure in
`P_{≤n}` (lines 1810-1814) is not formalized.  `P:mild-construction`'s
standing hypothesis `H:homog` plays no role in this display (the display is a
statement about Gaussian polynomials only) and is not carried. -/
theorem occupied_multiplication_paper {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    [IsProbabilityMeasure Pr] (g : Fin m → Ω → ℝ) (hind : iIndepFun g Pr)
    (hlaw : ∀ i, HasLaw (g i) (gaussianReal 0 1) Pr) (n : ℕ) (a : Fin m → ℝ)
    (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ n) :
    Integrable (fun ω => ((∑ i, a i * g i ω) * MvPolynomial.eval (fun i => g i ω) p) ^ 2) Pr ∧
      Integrable (fun ω => (∑ i, a i * g i ω) ^ 2) Pr ∧
      Integrable (fun ω => (MvPolynomial.eval (fun i => g i ω) p) ^ 2) Pr ∧
      √(∫ ω, ((∑ i, a i * g i ω) * MvPolynomial.eval (fun i => g i ω) p) ^ 2 ∂Pr) ≤
        2 * √((n : ℝ) + 1) * √(∫ ω, (∑ i, a i * g i ω) ^ 2 ∂Pr) *
          √(∫ ω, (MvPolynomial.eval (fun i => g i ω) p) ^ 2 ∂Pr) := by
  obtain ⟨h1, h2, h3, h4⟩ := occupied_multiplication n a p hp
  have hcH : Continuous fun x : Fin m → ℝ => ∑ i, a i * x i := by fun_prop
  have hcF : Continuous fun x : Fin m → ℝ => MvPolynomial.eval x p :=
    MvPolynomial.continuous_eval p
  have m1 := ((hcH.mul hcF).pow 2).aestronglyMeasurable (μ := GaussianIBP.stdPi m)
  have m2 := (hcH.pow 2).aestronglyMeasurable (μ := GaussianIBP.stdPi m)
  have m3 := (hcF.pow 2).aestronglyMeasurable (μ := GaussianIBP.stdPi m)
  refine ⟨(GaussianIBP.integrable_comp_iff_stdPi g hind hlaw m1).2 h1,
    (GaussianIBP.integrable_comp_iff_stdPi g hind hlaw m2).2 h2,
    (GaussianIBP.integrable_comp_iff_stdPi g hind hlaw m3).2 h3, ?_⟩
  rw [GaussianIBP.integral_comp_eq_stdPi g hind hlaw m1
      (h := fun x => ((∑ i, a i * x i) * MvPolynomial.eval x p) ^ 2),
    GaussianIBP.integral_comp_eq_stdPi g hind hlaw m2 (h := fun x => (∑ i, a i * x i) ^ 2),
    GaussianIBP.integral_comp_eq_stdPi g hind hlaw m3 (h := fun x => (MvPolynomial.eval x p) ^ 2)]
  have hB : 0 ≤ ∫ x, (∑ i, a i * x i) ^ 2 ∂GaussianIBP.stdPi m :=
    integral_nonneg fun x => sq_nonneg _
  have hC : 0 ≤ ∫ x, (MvPolynomial.eval x p) ^ 2 ∂GaussianIBP.stdPi m :=
    integral_nonneg fun x => sq_nonneg _
  have h2' : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc _ ≤ √(4 * ((n : ℝ) + 1) * (∫ x, (∑ i, a i * x i) ^ 2 ∂GaussianIBP.stdPi m) *
        ∫ x, (MvPolynomial.eval x p) ^ 2 ∂GaussianIBP.stdPi m) := Real.sqrt_le_sqrt h4
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by norm_num), h2']

/-! ### The degree-raising hypothesis of `HermiteWord.cut_eq_raw` -/

/-- Per-color degree support: `v` vanishes at every multi-index exceeding `d`
in some color. -/
def GoodDeg (d : Fin m → ℕ) (v : (Fin m → ℕ) → X) : Prop :=
  ∀ k, (∃ c, d c < k c) → v k = 0

/-- Per-color degree truncation (the cutoff `P` of `L:finite-word-cutoff`, in
the one-mode-per-color model). -/
def truncC (Nc : Fin m → ℕ) (v : (Fin m → ℕ) → X) : (Fin m → ℕ) → X :=
  fun k => if ∀ c, k c ≤ Nc c then v k else 0

omit [InnerProductSpace ℂ X] in
/-- Hypothesis `hv₀` of `cut_eq_raw`: the vacuum vector has zero degrees. -/
theorem goodDeg_vac (u : X) : GoodDeg (fun _ => 0) (vac (m := m) u) := by
  rintro k ⟨c, hc⟩
  have : k ≠ 0 := fun h => by simp [h] at hc
  simp [vac, this]

/-- **Hypothesis `hJ` of `cut_eq_raw` (degree raising)** for the concrete Fock
insertion `J i v = gmul i (K_i v)` (multiplication by `g_i` tensored with a
spatial operator `K_i`): it raises the degree of color `i` by one. -/
theorem goodDeg_insert (K : Fin m → X →L[ℂ] X) (d : Fin m → ℕ) (i : Fin m)
    (v : (Fin m → ℕ) → X) (hv : GoodDeg d v) :
    GoodDeg (fun c => d c + if c = i then 1 else 0) (gmul i (fun l => K i (v l))) := by
  rintro k ⟨c, hc⟩
  have h1 : v (k + unitIdx i) = 0 := hv _ ⟨c, by
    by_cases hci : c = i
    · subst hci; simp at hc ⊢; omega
    · simp [hci] at hc ⊢; omega⟩
  have h2 : v (k - unitIdx i) = 0 := hv _ ⟨c, by
    by_cases hci : c = i
    · subst hci; simp at hc ⊢; omega
    · simp [hci] at hc ⊢; omega⟩
  simp [gmul, cre, ann, h1, h2]

/-- Hypothesis `hF` of `cut_eq_raw`: frames acting on `X` preserve degrees. -/
theorem goodDeg_frame (T : X →L[ℂ] X) (d : Fin m → ℕ) (v : (Fin m → ℕ) → X)
    (hv : GoodDeg d v) : GoodDeg d (fun l => T (v l)) := fun k hk => by simp [hv k hk]

omit [InnerProductSpace ℂ X] in
/-- Hypothesis `hP` of `cut_eq_raw`: the per-color truncation fixes vectors whose
degrees are at most the cutoffs. -/
theorem truncC_eq (Nc d : Fin m → ℕ) (v : (Fin m → ℕ) → X) (hd : ∀ c, d c ≤ Nc c)
    (hv : GoodDeg d v) : truncC Nc v = v := by
  funext k
  unfold truncC
  split_ifs with h
  · rfl
  · simp only [not_forall, not_le] at h
    obtain ⟨c, hc⟩ := h
    exact (hv k ⟨c, by have := hd c; omega⟩).symm

end StratonovichHAMSecondMoment.FockForm
