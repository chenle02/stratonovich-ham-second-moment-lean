module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:raw-block-indexed-cone` (Indexed cone and terminal displacement) of
`notes/integrated_raw_block_lower.tex` (TeX lines 232--335 at revision
a284420), with its display `E:raw-block-positive-product`.

Class: inputs-supplied.  The lemma uses only the outputs of Section
`S:compact-mean-family` (`notes/integrated_compact_mean_family.tex`) for the
ground family.  They enter as ONE hypothesis structure `GroundFamily`, whose
fields are stated as the TeX states them (TeX lines and labels in each field's
doc comment):
* `P_σ(t)` bounded operators on a real normed space `F` (the physical flow of
  `S:compact-mean-family`, line 17; `E:compact-F-block`);
* vectors `e_σ`, functionals `ℓ_σ`, rank-one projections `Π_σ = e_σ ℓ_σ` and
  `Q_σ = I - Π_σ` (`E:compact-F-projection`, lines 270--272);
* rates `λ_σ > 0` (`E:compact-rate-gap` gives `√ε ≤ λ_σ`, line 51; only
  positivity is kept);
* `ℓ_σ(e_σ) = 1`, `P_σ(t)Π_σ = Π_σP_σ(t) = e^{λ_σ t}Π_σ`
  (`E:compact-F-eigen`, lines 277--281);
* the normalized complement `‖e^{-λ_σ t}P_σ(t)Q_σ‖ ≤ C_η e^{-ηt}` for every
  `0 < η < d_0` (`E:compact-normalized-complement`, lines 344--348), with
  `d_0 > 0` (`E:compact-rate-gap`); the identification
  `d_0 = inf_I(λ_σ - μ_σ)` is not needed and is not formalized;
* norm continuity of `σ ↦ e_σ` and `σ ↦ ℓ_σ` on `I = [0,1]` (lines
  280--281); continuity and uniform boundedness of `Π_σ`, and uniform
  boundedness of `e_σ, ℓ_σ`, are DERIVED here (compactness), not assumed;
* the margins `inf_I ℓ_σ(e_0) > 0`, `inf_I O_φ(e_σ) > 0`
  (`E:compact-positive-margins`, lines 283--286), with the data `e_0` and the
  bounded observable `O_φ` as fields.

The structure is no stronger than Propositions `P:compact-F-projection` and
`P:compact-F-complement` (with `P:compact-ground-family` for `λ_σ > 0`,
`d_0 > 0`): every field is one of their displayed conclusions, or a weakening
of one.  It does not encode `P_σ` as a semigroup, the spectral structure, or
`D8`; none of these is used by the lemma.

Side conditions made explicit:
* the TeX fixes `E_0 = ‖e_0‖ = 1`; here `‖e_0‖` is arbitrary (the constants are
  chosen with `max 1 ‖e_0‖`), a generalization;
* the operator families are `D : ℕ → ℝ → F →L[ℝ] F` with the closeness
  hypothesis only for `m ≤ N` and `u ∈ [0,B]` (no measurability, positivity or
  composition property, as the TeX says, line 249);
* the product `D_N(u)D_{N-1}(B)⋯D_0(B)e_0` is `D N u (chainState D B e0 N)`,
  with `chainState` the recursively defined state after `N` full blocks.

Proof route: the TeX cone induction (entrance, rebase, block, terminal), with
the TeX's order of constant choices (aperture `ϑ` first, then `B`, `ν`, `ω`,
and the five `ε_op` conditions).  The fallback split of the wave plan is used
as a STRUCTURING device only: `ConeConstants` records constants satisfying the
TeX's inequalities, `positive_product_of_constants` proves the product bound
for any such constants, and `exists_coneConstants` proves that they exist with
`a_* = inf_I ℓ_σ(e_0)` and `j_* = inf_I O_φ(e_σ)`.  The headline
`indexed_cone` combines both and gives the full existence statement of the TeX
with `c_* = a_* j_* / 4`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis

@[expose] public section

noncomputable section

set_option autoImplicit false

open Set Filter Topology

namespace StratonovichHAMSecondMoment.IndexedCone

/-- The family-parameter interval `I = [0,1]` of `S:compact-mean-family`
(TeX `integrated_compact_mean_family.tex`, line 4). -/
def paramI : Set ℝ := Icc 0 1

/-- `I = [0,1]` is compact (auxiliary to the Lean proof route). -/
theorem isCompact_paramI : IsCompact paramI := isCompact_Icc

/-- The C16 outputs used by `L:raw-block-indexed-cone`, supplied as one
hypothesis structure (inputs-supplied; see the module doc).  `P σ t` is the
flow `P_σ(t)`, `e σ` and `ell σ` are `e_σ` and `ℓ_σ`, `lam σ` is `λ_σ`, `e0`
is the data `e_0` and `obs` is the bounded observable `O_φ`. -/
structure GroundFamily (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The bounded flows `P_σ(t)` on `F` (`E:compact-F-block`). -/
  P : ℝ → ℝ → F →L[ℝ] F
  /-- The growing vectors `e_σ` (`E:compact-F-projection`). -/
  e : ℝ → F
  /-- The growing duals `ℓ_σ` (`E:compact-F-projection`). -/
  ell : ℝ → F →L[ℝ] ℝ
  /-- The rates `λ_σ = √(-E_1(σ))` (`P:compact-ground-family`). -/
  lam : ℝ → ℝ
  /-- The data `e_0` (`S:actual-raw-block-lower`, line 17). -/
  e0 : F
  /-- The bounded observable `O_φ` (`S:actual-raw-block-lower`, lines 16--17). -/
  obs : F →L[ℝ] ℝ
  /-- The uniform rate gap `d_0` (`E:compact-rate-gap`). -/
  d0 : ℝ
  /-- `λ_σ ≥ √ε > 0` on `I` (`E:compact-rate-gap`; positivity only). -/
  lam_pos : ∀ σ ∈ paramI, 0 < lam σ
  /-- `ℓ_σ(e_σ) = 1` (`E:compact-F-eigen`). -/
  ell_e : ∀ σ ∈ paramI, ell σ (e σ) = 1
  /-- `P_σ(t)Π_σ = e^{λ_σ t}Π_σ` (`E:compact-F-eigen`). -/
  P_Pi : ∀ σ ∈ paramI, ∀ t : ℝ, 0 ≤ t →
    (P σ t).comp ((ell σ).smulRight (e σ)) =
      Real.exp (lam σ * t) • (ell σ).smulRight (e σ)
  /-- `Π_σP_σ(t) = e^{λ_σ t}Π_σ` (`E:compact-F-eigen`). -/
  Pi_P : ∀ σ ∈ paramI, ∀ t : ℝ, 0 ≤ t →
    ((ell σ).smulRight (e σ)).comp (P σ t) =
      Real.exp (lam σ * t) • (ell σ).smulRight (e σ)
  /-- `d_0 > 0` (`E:compact-rate-gap`). -/
  d0_pos : 0 < d0
  /-- `‖e^{-λ_σ t}P_σ(t)Q_σ‖ ≤ C_η e^{-ηt}` uniformly over `σ ∈ I`, `t ≥ 0`,
  for every `0 < η < d_0` (`E:compact-normalized-complement`). -/
  normalized_complement : ∀ η : ℝ, 0 < η → η < d0 → ∃ C : ℝ,
    ∀ σ ∈ paramI, ∀ t : ℝ, 0 ≤ t →
      ‖Real.exp (-(lam σ * t)) •
          (P σ t).comp (ContinuousLinearMap.id ℝ F - (ell σ).smulRight (e σ))‖
        ≤ C * Real.exp (-(η * t))
  /-- Norm continuity of `σ ↦ e_σ` on `I` (`P:compact-F-projection`). -/
  e_cont : ContinuousOn e paramI
  /-- Norm continuity of `σ ↦ ℓ_σ` on `I` (`P:compact-F-projection`). -/
  ell_cont : ContinuousOn ell paramI
  /-- `inf_I ℓ_σ(e_0) > 0` (`E:compact-positive-margins`). -/
  margin_ell : 0 < ⨅ σ : paramI, ell σ e0
  /-- `inf_I O_φ(e_σ) > 0` (`E:compact-positive-margins`). -/
  margin_obs : 0 < ⨅ σ : paramI, obs (e σ)

namespace GroundFamily

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : GroundFamily F)

/-- The rank-one projection `Π_σ = e_σ ℓ_σ` (`E:compact-F-projection`). -/
def Pi (σ : ℝ) : F →L[ℝ] F := (G.ell σ).smulRight (G.e σ)

/-- The complementary projection `Q_σ = I - Π_σ` (`E:compact-F-projection`). -/
def Q (σ : ℝ) : F →L[ℝ] F := ContinuousLinearMap.id ℝ F - G.Pi σ

/-- The margin `a_* = inf_I ℓ_σ(e_0)` (TeX line 259). -/
def aStar : ℝ := ⨅ σ : paramI, G.ell σ G.e0

/-- The margin `j_* = inf_I O_φ(e_σ)` (TeX line 259). -/
def jStar : ℝ := ⨅ σ : paramI, G.obs (G.e σ)

/-- `Π_σ x = ℓ_σ(x) e_σ` (auxiliary to the Lean proof route). -/
theorem Pi_apply (σ : ℝ) (x : F) : G.Pi σ x = G.ell σ x • G.e σ := rfl

/-- `Q_σ x = x - ℓ_σ(x) e_σ` (auxiliary to the Lean proof route). -/
theorem Q_apply (σ : ℝ) (x : F) : G.Q σ x = x - G.ell σ x • G.e σ := rfl

/-- `ℓ_σ P_σ(t) = e^{λ_σ t} ℓ_σ` (from `E:compact-F-eigen`). -/
theorem ell_P {σ : ℝ} (hσ : σ ∈ paramI) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    G.ell σ (G.P σ t x) = Real.exp (G.lam σ * t) * G.ell σ x := by
  have h := congrArg (fun T : F →L[ℝ] F => G.ell σ (T x)) (G.Pi_P σ hσ t ht)
  simpa [ContinuousLinearMap.smulRight_apply, G.ell_e σ hσ] using h

/-- `P_σ(t)e_σ = e^{λ_σ t}e_σ` (from `E:compact-F-eigen`). -/
theorem P_e {σ : ℝ} (hσ : σ ∈ paramI) {t : ℝ} (ht : 0 ≤ t) :
    G.P σ t (G.e σ) = Real.exp (G.lam σ * t) • G.e σ := by
  have h := congrArg (fun T : F →L[ℝ] F => T (G.e σ)) (G.P_Pi σ hσ t ht)
  simpa [ContinuousLinearMap.smulRight_apply, G.ell_e σ hσ] using h

/-- `ℓ_σ Q_σ = 0` (TeX line 285, `ℓ_s(r) = 0`). -/
theorem ell_Q {σ : ℝ} (hσ : σ ∈ paramI) (x : F) : G.ell σ (G.Q σ x) = 0 := by
  simp [Q_apply, G.ell_e σ hσ]

/-- `Q_σ² = Q_σ` (TeX line 286, `r = Q_s z`). -/
theorem Q_Q {σ : ℝ} (hσ : σ ∈ paramI) (x : F) : G.Q σ (G.Q σ x) = G.Q σ x := by
  rw [Q_apply (x := G.Q σ x), G.ell_Q hσ, zero_smul, sub_zero]

/-- `z = ℓ_σ(z)e_σ + Q_σ z` (TeX line 285, `z = Ae_s + r`). -/
theorem decomp (σ : ℝ) (x : F) : x = G.ell σ x • G.e σ + G.Q σ x := by
  simp [Q_apply]

/-- `P_σ(t)Q_σ = Q_σP_σ(t)` (from `E:compact-F-eigen`). -/
theorem P_Q {σ : ℝ} (hσ : σ ∈ paramI) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    G.P σ t (G.Q σ x) = G.Q σ (G.P σ t x) := by
  rw [Q_apply, Q_apply, map_sub, map_smul, G.P_e hσ ht, G.ell_P hσ ht, smul_smul,
    mul_comm]

/-- `‖Q_σ‖ ≤ 1 + ‖Π_σ‖` (TeX line 263, `M_Q = 1 + M_P`). -/
theorem norm_Q_le (σ : ℝ) : ‖G.Q σ‖ ≤ 1 + ‖G.Pi σ‖ :=
  (norm_sub_le _ _).trans (by gcongr; exact ContinuousLinearMap.norm_id_le)

/-- `‖Π_σ‖ = ‖ℓ_σ‖‖e_σ‖` (auxiliary to the Lean proof route). -/
theorem norm_Pi (σ : ℝ) : ‖G.Pi σ‖ = ‖G.ell σ‖ * ‖G.e σ‖ :=
  ContinuousLinearMap.norm_smulRight_apply _ _

/-- `‖Π_b - Π_c‖ ≤ ‖e_b‖‖ℓ_b - ℓ_c‖ + ‖ℓ_c‖‖e_b - e_c‖` (auxiliary to the
Lean proof route: continuity of `Π` from that of `e, ℓ`). -/
theorem norm_Pi_sub_le (b c : ℝ) :
    ‖G.Pi b - G.Pi c‖ ≤ ‖G.e b‖ * ‖G.ell b - G.ell c‖ + ‖G.ell c‖ * ‖G.e b - G.e c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  have hx : (G.Pi b - G.Pi c) x =
      (G.ell b - G.ell c) x • G.e b + G.ell c x • (G.e b - G.e c) := by
    simp only [sub_apply, Pi_apply, sub_smul, smul_sub]
    abel
  rw [hx]
  calc ‖(G.ell b - G.ell c) x • G.e b + G.ell c x • (G.e b - G.e c)‖
      ≤ ‖(G.ell b - G.ell c) x‖ * ‖G.e b‖ + ‖G.ell c x‖ * ‖G.e b - G.e c‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ (‖G.ell b - G.ell c‖ * ‖x‖) * ‖G.e b‖ + (‖G.ell c‖ * ‖x‖) * ‖G.e b - G.e c‖ := by
        gcongr
        · exact ContinuousLinearMap.le_opNorm _ _
        · exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by ring

/-- `e^{λ_σ t} ≥ 1` for `t ≥ 0` (TeX line 302, "since `λ_c > 0`"). -/
theorem exp_ge_one {σ : ℝ} (hσ : σ ∈ paramI) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ Real.exp (G.lam σ * t) :=
  Real.one_le_exp (mul_nonneg (G.lam_pos σ hσ).le ht)

end GroundFamily

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The state after `m` full blocks, `D_{m-1}(B)⋯D_0(B)e_0`; the product of
`E:raw-block-positive-product` is `D N u (chainState D B e0 N)`. -/
def chainState (D : ℕ → ℝ → F →L[ℝ] F) (B : ℝ) (e0 : F) : ℕ → F
  | 0 => e0
  | m + 1 => D m B (chainState D B e0 m)

/-- Unfolding of `chainState` (auxiliary to the Lean proof route). -/
@[simp] theorem chainState_zero (D : ℕ → ℝ → F →L[ℝ] F) (B : ℝ) (e0 : F) :
    chainState D B e0 0 = e0 := rfl

/-- Unfolding of `chainState` (auxiliary to the Lean proof route). -/
@[simp] theorem chainState_succ (D : ℕ → ℝ → F →L[ℝ] F) (B : ℝ) (e0 : F) (m : ℕ) :
    chainState D B e0 (m + 1) = D m B (chainState D B e0 m) := rfl

/-- Constants satisfying relaxed, sufficient versions of the inequalities chosen
in the TeX proof (lines 254--281): any positive margins `a ≤ a_*`, `j ≤ j_*`,
nonnegative `C_gap, η_gap, ν` and bounds (the TeX fixes `C_gap ≥ 1`,
`η_gap, ν > 0`, `max(1, sup)` bounds; `exists_coneConstants` supplies them), bounds `M_e, M_ℓ, M_P,
H_obs`, the gap constants `C_gap, η_gap`, aperture `ϑ`, the block length `B`
with `q_B = C_gap e^{-η_gap B}`, `ν`, `ω` and `ε_op`.  Here `M_Q = 1 + M_P`,
`M_z = M_e + 1` and `E_0 = ‖e_0‖`. -/
structure ConeConstants (G : GroundFamily F) (ϱ : ℝ) where
  B : ℕ
  ω : ℝ
  ε : ℝ
  ϑ : ℝ
  ν : ℝ
  a : ℝ
  j : ℝ
  Me : ℝ
  Mell : ℝ
  MP : ℝ
  H : ℝ
  Cg : ℝ
  ηg : ℝ
  one_le_B : 1 ≤ B
  a_pos : 0 < a
  a_le : ∀ σ ∈ paramI, a ≤ G.ell σ G.e0
  j_pos : 0 < j
  j_le : ∀ σ ∈ paramI, j ≤ G.obs (G.e σ)
  Me_nonneg : 0 ≤ Me
  Me_bd : ∀ σ ∈ paramI, ‖G.e σ‖ ≤ Me
  Mell_nonneg : 0 ≤ Mell
  Mell_bd : ∀ σ ∈ paramI, ‖G.ell σ‖ ≤ Mell
  MP_nonneg : 0 ≤ MP
  MP_bd : ∀ σ ∈ paramI, ‖G.Pi σ‖ ≤ MP
  H_nonneg : 0 ≤ H
  H_bd : ‖G.obs‖ ≤ H
  Cg_nonneg : 0 ≤ Cg
  ηg_nonneg : 0 ≤ ηg
  gap : ∀ σ ∈ paramI, ∀ t : ℝ, 0 ≤ t →
    ‖Real.exp (-(G.lam σ * t)) • (G.P σ t).comp (G.Q σ)‖ ≤ Cg * Real.exp (-(ηg * t))
  ϑ_pos : 0 < ϑ
  ϑ_le_one : ϑ ≤ 1
  ϑ_aperture : 16 * H * Cg * ϑ ≤ j
  qB_le : Cg * Real.exp (-(ηg * B)) ≤ 1 / 8
  qB_entrance : 8 * (1 + MP) * ‖G.e0‖ * (Cg * Real.exp (-(ηg * B))) ≤ ϑ * a
  ν_nonneg : 0 ≤ ν
  ν_rho : ν * (Me + 1) ≤ ϱ / 2
  ν_ϑ : ν * (Me + 1) ≤ ϑ
  ν_quarter : ν * (Me + 1) ≤ 1 / 4
  ω_pos : 0 < ω
  ω_cont : ∀ b ∈ paramI, ∀ c ∈ paramI, |b - c| ≤ ω →
    ‖G.ell b - G.ell c‖ ≤ ν ∧ ‖G.Pi b - G.Pi c‖ ≤ ν
  ε_pos : 0 < ε
  ε_1 : Mell * ε * (Me + 1) ≤ ϱ / 2
  ε_2 : (1 + MP) * ε * (Me + 1) ≤ ϑ / 4
  ε_3 : Mell * ε * ‖G.e0‖ ≤ a / 2
  ε_4 : (1 + MP) * ε * ‖G.e0‖ ≤ ϑ * a / 8
  ε_5 : H * ε * (Me + 1) ≤ j / 8

namespace ConeConstants

variable {G : GroundFamily F} {ϱ : ℝ} (K : ConeConstants G ϱ)

/-- `‖Q_σ‖ ≤ M_Q` on `I` (TeX line 263). -/
theorem norm_Q_le {σ : ℝ} (hσ : σ ∈ paramI) : ‖G.Q σ‖ ≤ 1 + K.MP :=
  (G.norm_Q_le σ).trans (by linarith [K.MP_bd σ hσ])

/-- The gap bound applied to a vector: `‖P_σ(t)Q_σ y‖ ≤ e^{λ_σ t} g ‖y‖`
(auxiliary to the Lean proof route). -/
theorem norm_PQ_le {σ : ℝ} (hσ : σ ∈ paramI) {t : ℝ} (ht : 0 ≤ t) (y : F) :
    ‖G.P σ t (G.Q σ y)‖ ≤
      Real.exp (G.lam σ * t) * (K.Cg * Real.exp (-(K.ηg * t))) * ‖y‖ := by
  have h1 := (ContinuousLinearMap.le_opNorm
    (Real.exp (-(G.lam σ * t)) • (G.P σ t).comp (G.Q σ)) y).trans
    (mul_le_mul_of_nonneg_right (K.gap σ hσ t ht) (norm_nonneg y))
  rw [smul_apply, ContinuousLinearMap.comp_apply, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le] at h1
  have hE : Real.exp (G.lam σ * t) * Real.exp (-(G.lam σ * t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖G.P σ t (G.Q σ y)‖
      = Real.exp (G.lam σ * t) * (Real.exp (-(G.lam σ * t)) * ‖G.P σ t (G.Q σ y)‖) := by
        rw [← mul_assoc, hE, one_mul]
    _ ≤ Real.exp (G.lam σ * t) * (K.Cg * Real.exp (-(K.ηg * t)) * ‖y‖) := by
        gcongr
    _ = _ := by ring

/-- Perturbation of the amplitude: `ℓ_c(Dz) ≥ e^{λ_c t}ℓ_c(z) - M_ℓ ε ‖z‖`
(TeX lines 288, 304). -/
theorem step_ell {c : ℝ} (hc : c ∈ paramI) {t : ℝ} (ht : 0 ≤ t) {D : F →L[ℝ] F}
    (hD : ‖D - G.P c t‖ ≤ K.ε) (z : F) :
    Real.exp (G.lam c * t) * G.ell c z - K.Mell * K.ε * ‖z‖ ≤ G.ell c (D z) := by
  have hsplit : D z = G.P c t z + (D - G.P c t) z := by simp
  have hpert : |G.ell c ((D - G.P c t) z)| ≤ K.Mell * K.ε * ‖z‖ := by
    calc |G.ell c ((D - G.P c t) z)| = ‖G.ell c ((D - G.P c t) z)‖ := rfl
      _ ≤ ‖G.ell c‖ * (‖D - G.P c t‖ * ‖z‖) :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ K.Mell * (K.ε * ‖z‖) :=
          mul_le_mul (K.Mell_bd c hc) (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
            (by positivity) K.Mell_nonneg
      _ = _ := by ring
  rw [hsplit, map_add, G.ell_P hc ht]
  linarith [neg_abs_le (G.ell c ((D - G.P c t) z))]

/-- Perturbation of the residual:
`‖Q_c(Dz)‖ ≤ e^{λ_c t} g ‖Q_c z‖ + M_Q ε ‖z‖` (TeX lines 289, 310). -/
theorem step_Q {c : ℝ} (hc : c ∈ paramI) {t : ℝ} (ht : 0 ≤ t) {D : F →L[ℝ] F}
    (hD : ‖D - G.P c t‖ ≤ K.ε) (z : F) :
    ‖G.Q c (D z)‖ ≤ Real.exp (G.lam c * t) * (K.Cg * Real.exp (-(K.ηg * t))) * ‖G.Q c z‖ +
      (1 + K.MP) * K.ε * ‖z‖ := by
  have hsplit : G.Q c (D z) = G.P c t (G.Q c (G.Q c z)) + G.Q c ((D - G.P c t) z) := by
    rw [G.Q_Q hc, G.P_Q hc ht, ← map_add]
    simp
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add (K.norm_PQ_le hc ht _) ?_)
  calc ‖G.Q c ((D - G.P c t) z)‖ ≤ ‖G.Q c‖ * (‖D - G.P c t‖ * ‖z‖) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    _ ≤ (1 + K.MP) * (K.ε * ‖z‖) :=
        mul_le_mul (K.norm_Q_le hc) (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
          (by positivity) (by linarith [K.MP_nonneg])
    _ = _ := by ring

/-- Perturbation of the observable (TeX lines 324--328):
`O(Dz) ≥ e^{λ_c t}ℓ_c(z)O(e_c) - H e^{λ_c t} g ‖Q_c z‖ - H ε ‖z‖`. -/
theorem step_obs {c : ℝ} (hc : c ∈ paramI) {t : ℝ} (ht : 0 ≤ t) {D : F →L[ℝ] F}
    (hD : ‖D - G.P c t‖ ≤ K.ε) (z : F) :
    Real.exp (G.lam c * t) * (G.ell c z * G.obs (G.e c)) -
        K.H * (Real.exp (G.lam c * t) * (K.Cg * Real.exp (-(K.ηg * t))) * ‖G.Q c z‖) -
        K.H * K.ε * ‖z‖ ≤ G.obs (D z) := by
  have hPz : G.P c t z = (Real.exp (G.lam c * t) * G.ell c z) • G.e c +
      G.P c t (G.Q c (G.Q c z)) := by
    conv_lhs => rw [G.decomp c z]
    rw [map_add, map_smul, G.P_e hc ht, smul_smul, G.Q_Q hc, mul_comm]
  have hsplit : G.obs (D z) = Real.exp (G.lam c * t) * (G.ell c z * G.obs (G.e c)) +
      G.obs (G.P c t (G.Q c (G.Q c z))) + G.obs ((D - G.P c t) z) := by
    have : D z = G.P c t z + (D - G.P c t) z := by simp
    rw [this, map_add, hPz, map_add, map_smul, smul_eq_mul]
    ring
  have h1 : |G.obs (G.P c t (G.Q c (G.Q c z)))| ≤
      K.H * (Real.exp (G.lam c * t) * (K.Cg * Real.exp (-(K.ηg * t))) * ‖G.Q c z‖) := by
    calc |G.obs (G.P c t (G.Q c (G.Q c z)))| = ‖G.obs (G.P c t (G.Q c (G.Q c z)))‖ := rfl
      _ ≤ ‖G.obs‖ * ‖G.P c t (G.Q c (G.Q c z))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K.H * (Real.exp (G.lam c * t) * (K.Cg * Real.exp (-(K.ηg * t))) * ‖G.Q c z‖) := by
          gcongr
          · exact K.H_nonneg
          · exact K.H_bd
          · exact K.norm_PQ_le hc ht _
  have h2 : |G.obs ((D - G.P c t) z)| ≤ K.H * K.ε * ‖z‖ := by
    calc |G.obs ((D - G.P c t) z)| = ‖G.obs ((D - G.P c t) z)‖ := rfl
      _ ≤ ‖G.obs‖ * (‖D - G.P c t‖ * ‖z‖) :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ K.H * (K.ε * ‖z‖) :=
          mul_le_mul K.H_bd (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
            (by positivity) K.H_nonneg
      _ = _ := by ring
  rw [hsplit]
  linarith [neg_abs_le (G.obs (G.P c t (G.Q c (G.Q c z)))), neg_abs_le (G.obs ((D - G.P c t) z))]

/-- Rebase (TeX lines 293--299): an old-cone state `z` at `b` (amplitude
`A = ℓ_b(z) ≥ 0`, `‖Q_b z‖ ≤ ϑA`) and an adjacent `c` give `‖z‖ ≤ M_z A`,
`ℓ_c(z) ≥ (1 - νM_z)A` and `‖Q_c z‖ ≤ (ϑ + νM_z)A`. -/
theorem rebase {b c : ℝ} (hb : b ∈ paramI) (hc : c ∈ paramI) (hbc : |b - c| ≤ K.ω)
    {z : F} (hA : 0 ≤ G.ell b z) (hr : ‖G.Q b z‖ ≤ K.ϑ * G.ell b z) :
    ‖z‖ ≤ (K.Me + 1) * G.ell b z ∧
      (1 - K.ν * (K.Me + 1)) * G.ell b z ≤ G.ell c z ∧
      ‖G.Q c z‖ ≤ (K.ϑ + K.ν * (K.Me + 1)) * G.ell b z := by
  obtain ⟨hℓ, hPi⟩ := K.ω_cont b hb c hc hbc
  have hz : ‖z‖ ≤ (K.Me + 1) * G.ell b z := by
    have h0 := G.decomp b z
    calc ‖z‖ = ‖G.ell b z • G.e b + G.Q b z‖ := by rw [← h0]
      _ ≤ ‖G.ell b z • G.e b‖ + ‖G.Q b z‖ := norm_add_le _ _
      _ ≤ G.ell b z * K.Me + K.ϑ * G.ell b z := by
          rw [norm_smul, Real.norm_of_nonneg hA]
          gcongr
          exact K.Me_bd b hb
      _ ≤ (K.Me + 1) * G.ell b z := by nlinarith [K.ϑ_le_one]
  have hνz : ‖(G.ell b - G.ell c) z‖ ≤ K.ν * ((K.Me + 1) * G.ell b z) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hℓ hz (norm_nonneg _) K.ν_nonneg)
  have hPiz : ‖(G.Pi b - G.Pi c) z‖ ≤ K.ν * ((K.Me + 1) * G.ell b z) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hPi hz (norm_nonneg _) K.ν_nonneg)
  refine ⟨hz, ?_, ?_⟩
  · have h1 : G.ell c z = G.ell b z - (G.ell b - G.ell c) z := by simp
    have h2 := le_abs_self ((G.ell b - G.ell c) z)
    have h3 : |(G.ell b - G.ell c) z| ≤ K.ν * ((K.Me + 1) * G.ell b z) := hνz
    rw [h1]
    linarith
  · have h1 : G.Q c z = G.Q b z + (G.Pi b - G.Pi c) z := by
      simp only [GroundFamily.Q, sub_apply, ContinuousLinearMap.id_apply]
      abel
    rw [h1]
    calc ‖G.Q b z + (G.Pi b - G.Pi c) z‖ ≤ ‖G.Q b z‖ + ‖(G.Pi b - G.Pi c) z‖ := norm_add_le _ _
      _ ≤ K.ϑ * G.ell b z + K.ν * ((K.Me + 1) * G.ell b z) := add_le_add hr hPiz
      _ = _ := by ring

/-- `q_B ≥ 0` (auxiliary to the Lean proof route). -/
theorem qB_nonneg : 0 ≤ K.Cg * Real.exp (-(K.ηg * K.B)) :=
  mul_nonneg K.Cg_nonneg (Real.exp_pos _).le

/-- Entrance (TeX lines 287--291): `z_1 = D_0(B)e_0` lies in the cone at
`b = σ_0`, with amplitude at least `e^{λ_b B}a/2` (margin `a = K.a`; the TeX's
`a_*/2` is the case `a = a_*` from `exists_coneConstants`) and residual ratio at
most `ϑ/2`. -/
theorem entrance {b : ℝ} (hb : b ∈ paramI) {D : F →L[ℝ] F}
    (hD : ‖D - G.P b K.B‖ ≤ K.ε) :
    Real.exp (G.lam b * K.B) * (K.a / 2) ≤ G.ell b (D G.e0) ∧
      ‖G.Q b (D G.e0)‖ ≤ K.ϑ / 2 * G.ell b (D G.e0) := by
  have hB : (0 : ℝ) ≤ K.B := Nat.cast_nonneg _
  set E := Real.exp (G.lam b * K.B) with hEdef
  have hE1 : 1 ≤ E := G.exp_ge_one hb hB
  set q := K.Cg * Real.exp (-(K.ηg * K.B)) with hq
  have hq0 : 0 ≤ q := K.qB_nonneg
  have hℓ := K.step_ell hb hB hD G.e0
  have hQ := K.step_Q hb hB hD G.e0
  have ha := K.a_le b hb
  have hε3 := K.ε_3
  have hε4 := K.ε_4
  have hqe := K.qB_entrance
  have hMP := K.MP_nonneg
  have hMl := K.Mell_nonneg
  have hε := K.ε_pos
  have hnorm0 : 0 ≤ ‖G.e0‖ := norm_nonneg _
  have hQe0 : ‖G.Q b G.e0‖ ≤ (1 + K.MP) * ‖G.e0‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (K.norm_Q_le hb) hnorm0)
  have hpert0 : 0 ≤ K.Mell * K.ε * ‖G.e0‖ := by positivity
  have hamp : E * (K.a / 2) ≤ G.ell b (D G.e0) := by
    have h1 : E * K.a ≤ E * G.ell b G.e0 := mul_le_mul_of_nonneg_left ha (by linarith)
    have h2 : K.Mell * K.ε * ‖G.e0‖ ≤ E * (K.a / 2) := by nlinarith
    linarith
  refine ⟨hamp, ?_⟩
  have h3 : E * q * ‖G.Q b G.e0‖ ≤ E * (q * ((1 + K.MP) * ‖G.e0‖)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQe0 hq0) (by linarith)
  have h4 : (1 + K.MP) * K.ε * ‖G.e0‖ ≤ E * ((1 + K.MP) * K.ε * ‖G.e0‖) := by
    have : 0 ≤ (1 + K.MP) * K.ε * ‖G.e0‖ := by positivity
    nlinarith
  have h5 : q * ((1 + K.MP) * ‖G.e0‖) + (1 + K.MP) * K.ε * ‖G.e0‖ ≤ K.ϑ * K.a / 4 := by
    nlinarith
  have h6 : ‖G.Q b (D G.e0)‖ ≤ E * (K.ϑ * K.a / 4) := by
    have : E * (q * ((1 + K.MP) * ‖G.e0‖) + (1 + K.MP) * K.ε * ‖G.e0‖) ≤
        E * (K.ϑ * K.a / 4) := mul_le_mul_of_nonneg_left h5 (by linarith)
    nlinarith
  have h7 : E * (K.ϑ * K.a / 4) = K.ϑ / 2 * (E * (K.a / 2)) := by ring
  rw [h7] at h6
  exact h6.trans (mul_le_mul_of_nonneg_left hamp (by linarith [K.ϑ_pos]))

/-- One full block (TeX lines 300--318): from an old-cone state at `b`
(amplitude `A`) and an adjacent index `c`, the state `D z`, `D` close to
`P_c(B)`, lies in the cone at `c` with amplitude at least
`e^{λ_c B}(1 - ϱ)A`. -/
theorem block (hϱ : ϱ < 1 / 2) {b c : ℝ} (hb : b ∈ paramI) (hc : c ∈ paramI)
    (hbc : |b - c| ≤ K.ω) {z : F} (hA : 0 < G.ell b z) (hr : ‖G.Q b z‖ ≤ K.ϑ * G.ell b z)
    {D : F →L[ℝ] F} (hD : ‖D - G.P c K.B‖ ≤ K.ε) :
    Real.exp (G.lam c * K.B) * ((1 - ϱ) * G.ell b z) ≤ G.ell c (D z) ∧
      ‖G.Q c (D z)‖ ≤ K.ϑ * G.ell c (D z) := by
  have hB : (0 : ℝ) ≤ K.B := Nat.cast_nonneg _
  obtain ⟨hz, hℓc, hQc⟩ := K.rebase hb hc hbc hA.le hr
  set A := G.ell b z with hAdef
  set E := Real.exp (G.lam c * K.B) with hEdef
  have hE1 : 1 ≤ E := G.exp_ge_one hc hB
  set q := K.Cg * Real.exp (-(K.ηg * K.B)) with hq
  have hq0 : 0 ≤ q := K.qB_nonneg
  have hq8 : q ≤ 1 / 8 := K.qB_le
  set Mz := K.Me + 1 with hMz
  have hℓ := K.step_ell hc hB hD z
  have hQ := K.step_Q hc hB hD z
  have hε1 := K.ε_1
  have hε2 := K.ε_2
  have hνρ := K.ν_rho
  have hνϑ := K.ν_ϑ
  have hν0 : 0 ≤ K.ν * Mz := mul_nonneg K.ν_nonneg (by linarith [K.Me_nonneg])
  have hMl := K.Mell_nonneg
  have hMP := K.MP_nonneg
  have hε := K.ε_pos
  have hϑ := K.ϑ_pos
  have hMz0 : 0 ≤ Mz := by linarith [K.Me_nonneg]
  have hE0 : 0 ≤ E := by linarith
  -- amplitude
  have hamp : E * ((1 - ϱ) * A) ≤ G.ell c (D z) := by
    have h1 : E * ((1 - K.ν * Mz) * A) ≤ E * G.ell c z :=
      mul_le_mul_of_nonneg_left hℓc hE0
    have h2 : K.Mell * K.ε * ‖z‖ ≤ K.Mell * K.ε * Mz * A := by
      rw [mul_assoc (K.Mell * K.ε) Mz A]
      exact mul_le_mul_of_nonneg_left hz (by positivity)
    have h3 : K.Mell * K.ε * Mz * A ≤ E * (K.Mell * K.ε * Mz * A) :=
      le_mul_of_one_le_left (by positivity) hE1
    have hcoef : 1 - ϱ ≤ 1 - K.ν * Mz - K.Mell * K.ε * Mz := by linarith
    have h4 : (1 - ϱ) * A ≤ (1 - K.ν * Mz - K.Mell * K.ε * Mz) * A :=
      mul_le_mul_of_nonneg_right hcoef hA.le
    have h5 : E * ((1 - ϱ) * A) ≤ E * ((1 - K.ν * Mz - K.Mell * K.ε * Mz) * A) :=
      mul_le_mul_of_nonneg_left h4 hE0
    have h6 : E * ((1 - K.ν * Mz - K.Mell * K.ε * Mz) * A) =
        E * ((1 - K.ν * Mz) * A) - E * (K.Mell * K.ε * Mz * A) := by ring
    linarith
  refine ⟨hamp, ?_⟩
  -- residual
  have hQ1 : E * q * ‖G.Q c z‖ ≤ E * (q * ((K.ϑ + K.ν * Mz) * A)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQc hq0) hE0
  have hQ2 : (1 + K.MP) * K.ε * ‖z‖ ≤ E * ((1 + K.MP) * K.ε * Mz * A) := by
    have h0 : (1 + K.MP) * K.ε * ‖z‖ ≤ (1 + K.MP) * K.ε * Mz * A := by
      rw [mul_assoc ((1 + K.MP) * K.ε) Mz A]
      exact mul_le_mul_of_nonneg_left hz (by positivity)
    exact h0.trans (le_mul_of_one_le_left (by positivity) hE1)
  have hsum : K.ϑ + K.ν * Mz ≤ 2 * K.ϑ := by linarith
  have hq1 : q * (K.ϑ + K.ν * Mz) ≤ K.ϑ / 4 := by
    have := mul_le_mul hq8 hsum (by positivity) (by norm_num)
    linarith
  have hQ3 : q * ((K.ϑ + K.ν * Mz) * A) + (1 + K.MP) * K.ε * Mz * A ≤ K.ϑ / 2 * A := by
    have e1 : q * ((K.ϑ + K.ν * Mz) * A) = (q * (K.ϑ + K.ν * Mz)) * A := by ring
    have e2 : (1 + K.MP) * K.ε * Mz * A = ((1 + K.MP) * K.ε * Mz) * A := by ring
    rw [e1, e2, ← add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hA.le
  have hQ4 : ‖G.Q c (D z)‖ ≤ E * (K.ϑ / 2 * A) := by
    have h := mul_le_mul_of_nonneg_left hQ3 hE0
    have e3 : E * (q * ((K.ϑ + K.ν * Mz) * A) + (1 + K.MP) * K.ε * Mz * A) =
        E * (q * ((K.ϑ + K.ν * Mz) * A)) + E * ((1 + K.MP) * K.ε * Mz * A) := by ring
    linarith
  have hhalf : E * (K.ϑ / 2 * A) ≤ K.ϑ * (E * ((1 - ϱ) * A)) := by
    have e4 : K.ϑ * (E * ((1 - ϱ) * A)) - E * (K.ϑ / 2 * A) = (K.ϑ * E * A) * (1 / 2 - ϱ) := by
      ring
    have : 0 ≤ (K.ϑ * E * A) * (1 / 2 - ϱ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hϑ.le hE0) hA.le) (by linarith)
    linarith
  calc ‖G.Q c (D z)‖ ≤ E * (K.ϑ / 2 * A) := hQ4
    _ ≤ K.ϑ * (E * ((1 - ϱ) * A)) := hhalf
    _ ≤ K.ϑ * G.ell c (D z) := mul_le_mul_of_nonneg_left hamp hϑ.le

/-- Terminal step (TeX lines 320--330): for `0 ≤ u`, an old-cone state at `b`
(amplitude `A`), an adjacent `c`, and `D` close to `P_c(u)`,
`O_φ(Dz) ≥ e^{λ_c u}(j/2)A` (margin `j = K.j`; the TeX's `j_*/2` is the case
`j = j_*` from `exists_coneConstants`). -/
theorem terminal {b c : ℝ} (hb : b ∈ paramI) (hc : c ∈ paramI) (hbc : |b - c| ≤ K.ω)
    {z : F} (hA : 0 ≤ G.ell b z) (hr : ‖G.Q b z‖ ≤ K.ϑ * G.ell b z)
    {u : ℝ} (hu : 0 ≤ u) {D : F →L[ℝ] F} (hD : ‖D - G.P c u‖ ≤ K.ε) :
    Real.exp (G.lam c * u) * (K.j / 2 * G.ell b z) ≤ G.obs (D z) := by
  obtain ⟨hz, hℓc, hQc⟩ := K.rebase hb hc hbc hA hr
  set A := G.ell b z with hAdef
  set E := Real.exp (G.lam c * u) with hEdef
  have hE1 : 1 ≤ E := G.exp_ge_one hc hu
  set g := K.Cg * Real.exp (-(K.ηg * u)) with hg
  have hg0 : 0 ≤ g := mul_nonneg K.Cg_nonneg (Real.exp_pos _).le
  have hgC : g ≤ K.Cg := by
    have : Real.exp (-(K.ηg * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [K.ηg_nonneg])
    nlinarith [K.Cg_nonneg]
  set Mz := K.Me + 1 with hMz
  have hO := K.step_obs hc hu hD z
  have hνq := K.ν_quarter
  have hνϑ := K.ν_ϑ
  have hν0 : 0 ≤ K.ν * Mz := mul_nonneg K.ν_nonneg (by linarith [K.Me_nonneg])
  have hj := K.j_le c hc
  have hj0 := K.j_pos
  have hH := K.H_nonneg
  have hϑ := K.ϑ_pos
  have hap := K.ϑ_aperture
  have hε5 := K.ε_5
  have hε := K.ε_pos
  -- ℓ_c(z) ≥ 3A/4 and ‖Q_c z‖ ≤ 2ϑA
  have hℓ3 : 3 / 4 * A ≤ G.ell c z := by nlinarith
  have hQ2 : ‖G.Q c z‖ ≤ 2 * K.ϑ * A := by nlinarith
  have t1 : E * (3 / 4 * A * K.j) ≤ E * (G.ell c z * G.obs (G.e c)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact mul_le_mul hℓ3 hj hj0.le (by linarith)
  have t2 : K.H * (E * g * ‖G.Q c z‖) ≤ E * (K.j / 8 * A) := by
    have h1 : K.H * (E * g * ‖G.Q c z‖) ≤ K.H * (E * K.Cg * (2 * K.ϑ * A)) := by
      apply mul_le_mul_of_nonneg_left _ hH
      exact mul_le_mul (mul_le_mul_of_nonneg_left hgC (by linarith)) hQ2 (norm_nonneg _)
        (mul_nonneg (by linarith) K.Cg_nonneg)
    have h2 : K.H * (E * K.Cg * (2 * K.ϑ * A)) = E * A * (2 * (K.H * K.Cg * K.ϑ)) := by ring
    have h3 : 2 * (K.H * K.Cg * K.ϑ) ≤ K.j / 8 := by nlinarith
    have h4 : 0 ≤ E * A := mul_nonneg (by linarith) hA
    nlinarith
  have t3 : K.H * K.ε * ‖z‖ ≤ E * (K.j / 8 * A) := by
    have h1 : K.H * K.ε * ‖z‖ ≤ K.H * K.ε * (Mz * A) :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    have h2 : K.H * K.ε * (Mz * A) ≤ K.j / 8 * A := by
      have : K.H * K.ε * (Mz * A) = (K.H * K.ε * Mz) * A := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hε5 hA
    have h3 : 0 ≤ K.j / 8 * A := by positivity
    nlinarith
  have : E * (K.j / 2 * A) = E * (3 / 4 * A * K.j) - E * (K.j / 8 * A) - E * (K.j / 8 * A) := by
    ring
  rw [this]
  linarith

/-- The cone induction (TeX lines 285--318, 330--332): for `m + 1 ≤ N` the
state after `m + 1` full blocks lies in the cone at `σ_m`, with amplitude at
least `(a/2)(1-ϱ)^m exp(B Σ_{k ≤ m} λ_{σ_k})`. -/
theorem chain_cone (hϱ : ϱ < 1 / 2) {N : ℕ} {σ : ℕ → ℝ} (hσ : ∀ m ≤ N, σ m ∈ paramI)
    (hadj : ∀ m < N, |σ (m + 1) - σ m| ≤ K.ω) {D : ℕ → ℝ → F →L[ℝ] F}
    (hD : ∀ m ≤ N, ∀ u ∈ Icc (0 : ℝ) K.B, ‖D m u - G.P (σ m) u‖ ≤ K.ε) :
    ∀ m : ℕ, m + 1 ≤ N →
      K.a / 2 * (1 - ϱ) ^ m *
          Real.exp ((K.B : ℝ) * ∑ k ∈ Finset.range (m + 1), G.lam (σ k)) ≤
        G.ell (σ m) (chainState D K.B G.e0 (m + 1)) ∧
      0 < G.ell (σ m) (chainState D K.B G.e0 (m + 1)) ∧
      ‖G.Q (σ m) (chainState D K.B G.e0 (m + 1))‖ ≤
        K.ϑ * G.ell (σ m) (chainState D K.B G.e0 (m + 1)) := by
  have hBmem : (K.B : ℝ) ∈ Icc (0 : ℝ) K.B := ⟨Nat.cast_nonneg _, le_rfl⟩
  have h1ϱ : 0 < 1 - ϱ := by linarith
  intro m
  induction m with
  | zero =>
    intro hN
    have hσ0 := hσ 0 (by omega)
    obtain ⟨hamp, hres⟩ := K.entrance hσ0 (hD 0 (by omega) _ hBmem)
    have hpos : 0 < Real.exp (G.lam (σ 0) * K.B) * (K.a / 2) :=
      mul_pos (Real.exp_pos _) (by linarith [K.a_pos])
    have hpos' : 0 < G.ell (σ 0) (chainState D K.B G.e0 1) := lt_of_lt_of_le hpos hamp
    refine ⟨?_, hpos', ?_⟩
    · simp only [zero_add, pow_zero, mul_one, Finset.sum_range_one, chainState_succ,
        chainState_zero]
      calc K.a / 2 * Real.exp (K.B * G.lam (σ 0))
          = Real.exp (G.lam (σ 0) * K.B) * (K.a / 2) := by rw [mul_comm (K.B : ℝ)]; ring
        _ ≤ _ := hamp
    · simp only [chainState_succ, chainState_zero] at hres ⊢
      have : K.ϑ / 2 * G.ell (σ 0) (D 0 K.B G.e0) ≤ K.ϑ * G.ell (σ 0) (D 0 K.B G.e0) := by
        have := K.ϑ_pos
        simp only [chainState_succ, chainState_zero] at hpos'
        nlinarith
      exact hres.trans this
  | succ m ih =>
    intro hN
    obtain ⟨hamp, hpos, hres⟩ := ih (by omega)
    have hb := hσ m (by omega)
    have hc := hσ (m + 1) (by omega)
    have hbc : |σ m - σ (m + 1)| ≤ K.ω := by
      rw [abs_sub_comm]; exact hadj m (by omega)
    obtain ⟨hamp', hres'⟩ := K.block hϱ hb hc hbc hpos hres (hD (m + 1) (by omega) _ hBmem)
    set z := chainState D K.B G.e0 (m + 1)
    have hz2 : chainState D K.B G.e0 (m + 1 + 1) = D (m + 1) K.B z := rfl
    rw [hz2]
    have hpos2 : 0 < G.ell (σ (m + 1)) (D (m + 1) K.B z) :=
      lt_of_lt_of_le (mul_pos (Real.exp_pos _) (mul_pos h1ϱ hpos)) hamp'
    refine ⟨?_, hpos2, hres'⟩
    rw [Finset.sum_range_succ, mul_add, Real.exp_add, pow_succ]
    calc K.a / 2 * ((1 - ϱ) ^ m * (1 - ϱ)) *
          (Real.exp (K.B * ∑ k ∈ Finset.range (m + 1), G.lam (σ k)) *
            Real.exp (K.B * G.lam (σ (m + 1))))
        = Real.exp (G.lam (σ (m + 1)) * K.B) *
            ((1 - ϱ) * (K.a / 2 * (1 - ϱ) ^ m *
              Real.exp (K.B * ∑ k ∈ Finset.range (m + 1), G.lam (σ k)))) := by
          rw [mul_comm (K.B : ℝ) (G.lam (σ (m + 1)))]; ring
      _ ≤ Real.exp (G.lam (σ (m + 1)) * K.B) * ((1 - ϱ) * G.ell (σ m) z) := by
          gcongr
      _ ≤ _ := hamp'

/-- `E:raw-block-positive-product` for given constants satisfying the TeX's
inequalities (fallback form of `L:raw-block-indexed-cone`), with
`c_* = a j / 4`. -/
theorem positive_product_of_constants (hϱ : ϱ < 1 / 2) {N : ℕ} (hN : 1 ≤ N)
    {σ : ℕ → ℝ} (hσ : ∀ m ≤ N, σ m ∈ paramI)
    (hadj : ∀ m < N, |σ (m + 1) - σ m| ≤ K.ω) {D : ℕ → ℝ → F →L[ℝ] F}
    (hD : ∀ m ≤ N, ∀ u ∈ Icc (0 : ℝ) K.B, ‖D m u - G.P (σ m) u‖ ≤ K.ε)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) K.B) :
    K.a * K.j / 4 * (1 - ϱ) ^ (N - 1) *
        Real.exp ((K.B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) ≤
      G.obs (D N u (chainState D K.B G.e0 N)) ∧
    0 < K.a * K.j / 4 * (1 - ϱ) ^ (N - 1) *
        Real.exp ((K.B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h1ϱ : 0 < 1 - ϱ := by linarith
  obtain ⟨hamp, hpos, hres⟩ := K.chain_cone hϱ hσ hadj hD n le_rfl
  have hb := hσ n (by omega)
  have hc := hσ (n + 1) le_rfl
  have hbc : |σ n - σ (n + 1)| ≤ K.ω := by rw [abs_sub_comm]; exact hadj n (by omega)
  have hterm := K.terminal hb hc hbc hpos.le hres hu.1 (hD (n + 1) le_rfl u hu)
  have hsimp : n + 1 - 1 = n := by omega
  rw [hsimp]
  refine ⟨?_, by
    have := K.a_pos; have := K.j_pos; positivity⟩
  rw [Real.exp_add]
  calc K.a * K.j / 4 * (1 - ϱ) ^ n *
        (Real.exp (K.B * ∑ m ∈ Finset.range (n + 1), G.lam (σ m)) *
          Real.exp (u * G.lam (σ (n + 1))))
      = Real.exp (G.lam (σ (n + 1)) * u) * (K.j / 2 *
          (K.a / 2 * (1 - ϱ) ^ n *
            Real.exp (K.B * ∑ m ∈ Finset.range (n + 1), G.lam (σ m)))) := by
        rw [mul_comm u]; ring
    _ ≤ Real.exp (G.lam (σ (n + 1)) * u) *
          (K.j / 2 * G.ell (σ n) (chainState D K.B G.e0 (n + 1))) := by
        have := K.j_pos
        gcongr
    _ ≤ _ := hterm

end ConeConstants

/-! ### Existence of the constants (TeX lines 254--282) -/

namespace GroundFamily

variable (G : GroundFamily F)

/-- Continuity of `σ ↦ ℓ_σ(e_0)` on `I` (auxiliary to the Lean proof route). -/
theorem ell_e0_continuousOn : ContinuousOn (fun σ => G.ell σ G.e0) paramI :=
  G.ell_cont.clm_apply continuousOn_const

/-- Continuity of `σ ↦ O_φ(e_σ)` on `I` (auxiliary to the Lean proof route). -/
theorem obs_e_continuousOn : ContinuousOn (fun σ => G.obs (G.e σ)) paramI :=
  G.obs.continuous.comp_continuousOn G.e_cont

/-- `a_* ≤ ℓ_σ(e_0)` on `I` (the infimum is over a bounded set by
compactness). -/
theorem aStar_le {σ : ℝ} (hσ : σ ∈ paramI) : G.aStar ≤ G.ell σ G.e0 := by
  have hbdd := isCompact_paramI.bddBelow_image G.ell_e0_continuousOn
  rw [image_eq_range] at hbdd
  exact ciInf_le hbdd ⟨σ, hσ⟩

/-- `j_* ≤ O_φ(e_σ)` on `I`. -/
theorem jStar_le {σ : ℝ} (hσ : σ ∈ paramI) : G.jStar ≤ G.obs (G.e σ) := by
  have hbdd := isCompact_paramI.bddBelow_image G.obs_e_continuousOn
  rw [image_eq_range] at hbdd
  exact ciInf_le hbdd ⟨σ, hσ⟩

/-- Uniform boundedness and continuity of `Π_σ` on `I` (stated in
`P:compact-F-projection`; derived here from the continuity of `e_σ, ℓ_σ`). -/
theorem Pi_bounded_continuous :
    (∃ M : ℝ, ∀ σ ∈ paramI, ‖G.Pi σ‖ ≤ M) ∧ ContinuousOn G.Pi paramI := by
  obtain ⟨C1, hC1⟩ := isCompact_paramI.exists_bound_of_continuousOn G.e_cont
  obtain ⟨C2, hC2⟩ := isCompact_paramI.exists_bound_of_continuousOn G.ell_cont
  refine ⟨⟨C2 * C1, fun σ hσ => ?_⟩, ?_⟩
  · rw [G.norm_Pi]
    exact mul_le_mul (hC2 σ hσ) (hC1 σ hσ) (norm_nonneg _) ((norm_nonneg _).trans (hC2 σ hσ))
  · intro σ hσ
    rw [Metric.continuousWithinAt_iff]
    intro r hr
    have hM1 : 0 ≤ max 1 C1 := by positivity
    have hM2 : 0 < max 1 C2 := by positivity
    have he := Metric.continuousWithinAt_iff.mp (G.e_cont σ hσ) (r / (2 * max 1 C2))
      (by positivity)
    have hl := Metric.continuousWithinAt_iff.mp (G.ell_cont σ hσ) (r / (2 * max 1 C1 + 2))
      (by positivity)
    obtain ⟨δ1, hδ1, h1⟩ := he
    obtain ⟨δ2, hδ2, h2⟩ := hl
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun {x} hx hxd => ?_⟩
    have hx1 := h1 hx (lt_of_lt_of_le hxd (min_le_left _ _))
    have hx2 := h2 hx (lt_of_lt_of_le hxd (min_le_right _ _))
    rw [dist_eq_norm] at hx1 hx2 ⊢
    have hb := G.norm_Pi_sub_le x σ
    have hex : ‖G.e x‖ ≤ max 1 C1 := (hC1 x hx).trans (le_max_right _ _)
    have hlσ : ‖G.ell σ‖ ≤ max 1 C2 := (hC2 σ hσ).trans (le_max_right _ _)
    have t1 : ‖G.e x‖ * ‖G.ell x - G.ell σ‖ ≤ max 1 C1 * (r / (2 * max 1 C1 + 2)) :=
      mul_le_mul hex hx2.le (norm_nonneg _) hM1
    have t2 : ‖G.ell σ‖ * ‖G.e x - G.e σ‖ ≤ max 1 C2 * (r / (2 * max 1 C2)) :=
      mul_le_mul hlσ hx1.le (norm_nonneg _) hM2.le
    have t3 : max 1 C1 * (r / (2 * max 1 C1 + 2)) < r / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have t4 : max 1 C2 * (r / (2 * max 1 C2)) = r / 2 := by
      field_simp
    linarith

end GroundFamily

/-- Existence of constants satisfying the TeX's inequalities, in the TeX's order
(lines 254--282): `a = a_*`, `j = j_*`, `M_e = max(1, sup‖e_σ‖)`-type bounds,
`C_gap ≥ 1`, `η_gap = d_0/2`, the aperture
`ϑ = min(1, j_*/(16 H_obs C_gap))` first, then the integer `B ≥ 1`, then `ν`,
`ω` (uniform continuity on compact `I`) and `ε_op`. -/
theorem exists_coneConstants (G : GroundFamily F) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    ∃ K : ConeConstants G ϱ, K.a = G.aStar ∧ K.j = G.jStar := by
  have ha : 0 < G.aStar := G.margin_ell
  have hj : 0 < G.jStar := G.margin_obs
  obtain ⟨C1, hC1⟩ := isCompact_paramI.exists_bound_of_continuousOn G.e_cont
  obtain ⟨C2, hC2⟩ := isCompact_paramI.exists_bound_of_continuousOn G.ell_cont
  have hd0 := G.d0_pos
  obtain ⟨C, hC⟩ := G.normalized_complement (G.d0 / 2) (by linarith) (by linarith)
  -- bounds
  set Me := max 1 C1 with hMe
  set Mell := max 1 C2 with hMell
  set MP := Mell * Me with hMP
  set H := max 1 ‖G.obs‖ with hH
  set Cg := max 1 C with hCg
  set ηg := G.d0 / 2 with hηg
  have hMe1 : 1 ≤ Me := le_max_left _ _
  have hMell1 : 1 ≤ Mell := le_max_left _ _
  have hH1 : 1 ≤ H := le_max_left _ _
  have hCg1 : 1 ≤ Cg := le_max_left _ _
  have hηg : 0 < ηg := by positivity
  have hMP0 : 0 ≤ MP := by positivity
  -- aperture first
  set ϑ := min 1 (G.jStar / (16 * H * Cg)) with hϑ
  have hϑ0 : 0 < ϑ := lt_min one_pos (by positivity)
  have hϑ1 : ϑ ≤ 1 := min_le_left _ _
  have hϑap : 16 * H * Cg * ϑ ≤ G.jStar := by
    have h := min_le_right 1 (G.jStar / (16 * H * Cg))
    have hpos : 0 < 16 * H * Cg := by positivity
    calc 16 * H * Cg * ϑ ≤ 16 * H * Cg * (G.jStar / (16 * H * Cg)) :=
          mul_le_mul_of_nonneg_left h hpos.le
      _ = G.jStar := by field_simp
  -- block length
  set E0 := max 1 ‖G.e0‖ with hE0
  have hE01 : 1 ≤ E0 := le_max_left _ _
  have hE0n : ‖G.e0‖ ≤ E0 := le_max_right _ _
  set MQ := 1 + MP with hMQ
  have hMQ1 : 1 ≤ MQ := by linarith
  set qt := min (1 / 8) (ϑ * G.aStar / (8 * MQ * E0)) with hqt
  have hqt0 : 0 < qt := lt_min (by norm_num) (by positivity)
  obtain ⟨B0, hB0⟩ := exists_nat_ge (Cg / (qt * ηg))
  set B : ℕ := max B0 1 with hB
  have hB1 : 1 ≤ B := le_max_right _ _
  have hBB0 : (B0 : ℝ) ≤ B := by exact_mod_cast le_max_left B0 1
  have hqB : Cg * Real.exp (-(ηg * B)) ≤ qt := by
    set x := ηg * (B : ℝ) with hx
    have hx0 : 0 ≤ x := by positivity
    have hexp := Real.add_one_le_exp x
    have hinv : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have hpos : 0 < Real.exp (-x) := Real.exp_pos _
    have hex : Real.exp (-x) * x ≤ 1 := by nlinarith
    have hCx : Cg ≤ qt * x := by
      have h1 : Cg / (qt * ηg) ≤ B := hB0.trans hBB0
      rw [div_le_iff₀ (by positivity)] at h1
      linarith
    calc Cg * Real.exp (-x) ≤ qt * x * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hCx hpos.le
      _ = qt * (Real.exp (-x) * x) := by ring
      _ ≤ qt * 1 := mul_le_mul_of_nonneg_left hex hqt0.le
      _ = qt := mul_one _
  have hq0 : 0 ≤ Cg * Real.exp (-(ηg * B)) := by positivity
  -- ν
  set Mz := Me + 1 with hMz
  have hMz0 : 0 < Mz := by linarith
  set ν := min (ϱ / 2) (min ϑ (1 / 4)) / Mz with hν
  have hν0 : 0 < ν := by
    have : 0 < min (ϱ / 2) (min ϑ (1 / 4)) := lt_min (by linarith) (lt_min hϑ0 (by norm_num))
    positivity
  have hνMz : ν * Mz = min (ϱ / 2) (min ϑ (1 / 4)) := by
    rw [hν]; field_simp
  -- ω
  have hucl := isCompact_paramI.uniformContinuousOn_of_continuous G.ell_cont
  have huce := isCompact_paramI.uniformContinuousOn_of_continuous G.e_cont
  rw [Metric.uniformContinuousOn_iff_le] at hucl huce
  obtain ⟨δ1, hδ1, hl⟩ := hucl (ν / (2 * Me)) (by positivity)
  obtain ⟨δ2, hδ2, he⟩ := huce (ν / (2 * Mell)) (by positivity)
  set ω := min δ1 δ2 with hω
  have hωcont : ∀ b ∈ paramI, ∀ c ∈ paramI, |b - c| ≤ ω →
      ‖G.ell b - G.ell c‖ ≤ ν ∧ ‖G.Pi b - G.Pi c‖ ≤ ν := by
    intro b hb c hc hbc
    have hd : dist b c = |b - c| := Real.dist_eq b c
    have h1 := hl b hb c hc (by rw [hd]; exact hbc.trans (min_le_left _ _))
    have h2 := he b hb c hc (by rw [hd]; exact hbc.trans (min_le_right _ _))
    rw [dist_eq_norm] at h1 h2
    have hlν : ν / (2 * Me) ≤ ν := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    refine ⟨h1.trans hlν, ?_⟩
    have heb : ‖G.e b‖ ≤ Me := (hC1 b hb).trans (le_max_right _ _)
    have hlc : ‖G.ell c‖ ≤ Mell := (hC2 c hc).trans (le_max_right _ _)
    have t1 : ‖G.e b‖ * ‖G.ell b - G.ell c‖ ≤ Me * (ν / (2 * Me)) :=
      mul_le_mul heb h1 (norm_nonneg _) (by linarith)
    have t2 : ‖G.ell c‖ * ‖G.e b - G.e c‖ ≤ Mell * (ν / (2 * Mell)) :=
      mul_le_mul hlc h2 (norm_nonneg _) (by linarith)
    have t3 : Me * (ν / (2 * Me)) = ν / 2 := by field_simp
    have t4 : Mell * (ν / (2 * Mell)) = ν / 2 := by field_simp
    linarith [G.norm_Pi_sub_le b c]
  -- ε_op: the five smallness conditions
  set r1 := ϱ / (2 * Mell * Mz)
  set r2 := ϑ / (4 * MQ * Mz)
  set r3 := G.aStar / (2 * Mell * E0)
  set r4 := ϑ * G.aStar / (8 * MQ * E0)
  set r5 := G.jStar / (8 * H * Mz)
  set ε := min r1 (min r2 (min r3 (min r4 r5))) with hε
  have hε0 : 0 < ε := lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hε1 : ε ≤ r1 := min_le_left _ _
  have hε2 : ε ≤ r2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ r3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε4 : ε ≤ r4 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε5 : ε ≤ r5 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  rw [le_div_iff₀ (by positivity)] at hε1 hε2 hε3 hε4 hε5
  refine ⟨{
    B := B, ω := ω, ε := ε, ϑ := ϑ, ν := ν, a := G.aStar, j := G.jStar, Me := Me,
    Mell := Mell, MP := MP, H := H, Cg := Cg, ηg := ηg
    one_le_B := hB1
    a_pos := ha
    a_le := fun σ hσ => G.aStar_le hσ
    j_pos := hj
    j_le := fun σ hσ => G.jStar_le hσ
    Me_nonneg := by linarith
    Me_bd := fun σ hσ => (hC1 σ hσ).trans (le_max_right _ _)
    Mell_nonneg := by linarith
    Mell_bd := fun σ hσ => (hC2 σ hσ).trans (le_max_right _ _)
    MP_nonneg := hMP0
    MP_bd := fun σ hσ => by
      rw [G.norm_Pi]
      exact mul_le_mul ((hC2 σ hσ).trans (le_max_right _ _))
        ((hC1 σ hσ).trans (le_max_right _ _)) (norm_nonneg _) (by linarith)
    H_nonneg := by linarith
    H_bd := le_max_right _ _
    Cg_nonneg := by linarith
    ηg_nonneg := hηg.le
    gap := fun σ hσ t ht =>
      (hC σ hσ t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
    ϑ_pos := hϑ0
    ϑ_le_one := hϑ1
    ϑ_aperture := hϑap
    qB_le := hqB.trans (min_le_left _ _)
    qB_entrance := by
      have h1 : 8 * MQ * ‖G.e0‖ * (Cg * Real.exp (-(ηg * B))) ≤ 8 * MQ * E0 * qt := by
        apply mul_le_mul _ hqB hq0 (by positivity)
        exact mul_le_mul_of_nonneg_left hE0n (by positivity)
      have h2 : qt ≤ ϑ * G.aStar / (8 * MQ * E0) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h2
      linarith
    ν_nonneg := hν0.le
    ν_rho := by rw [hνMz]; exact min_le_left _ _
    ν_ϑ := by rw [hνMz]; exact (min_le_right _ _).trans (min_le_left _ _)
    ν_quarter := by rw [hνMz]; exact (min_le_right _ _).trans (min_le_right _ _)
    ω_pos := lt_min hδ1 hδ2
    ω_cont := hωcont
    ε_pos := hε0
    ε_1 := by linarith
    ε_2 := by linarith
    ε_3 := by
      have : Mell * ε * ‖G.e0‖ ≤ Mell * ε * E0 :=
        mul_le_mul_of_nonneg_left hE0n (by positivity)
      linarith
    ε_4 := by
      have : MQ * ε * ‖G.e0‖ ≤ MQ * ε * E0 :=
        mul_le_mul_of_nonneg_left hE0n (by positivity)
      linarith
    ε_5 := by linarith }, rfl, rfl⟩

/-- **`L:raw-block-indexed-cone`** (TeX lines 232--251, display
`E:raw-block-positive-product`), for a supplied ground family: for
`0 < ϱ < 1/2` there are an integer `B ≥ 1` and positive `ω, ε_op, c_*`, with
`c_* = a_* j_*/4`, such that for every `N ≥ 1`, every chain
`σ_0,…,σ_N ∈ I` with adjacent distances at most `ω`, and every family
`D_m(u)` within `ε_op` of `P_{σ_m}(u)` (`m ≤ N`, `0 ≤ u ≤ B`),
`O_φ D_N(u)D_{N-1}(B)⋯D_0(B)e_0 ≥ c_*(1-ϱ)^{N-1}exp(BΣ_{m<N}λ_{σ_m} + uλ_{σ_N}) > 0`
for `0 ≤ u ≤ B`. -/
theorem indexed_cone (G : GroundFamily F) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ < 1 / 2) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ ω : ℝ, 0 < ω ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ cStar : ℝ, 0 < cStar ∧
      cStar = G.aStar * G.jStar / 4 ∧
      ∀ N : ℕ, 1 ≤ N → ∀ σ : ℕ → ℝ, (∀ m ≤ N, σ m ∈ paramI) →
        (∀ m < N, |σ (m + 1) - σ m| ≤ ω) →
        ∀ D : ℕ → ℝ → F →L[ℝ] F,
          (∀ m ≤ N, ∀ u ∈ Icc (0 : ℝ) B, ‖D m u - G.P (σ m) u‖ ≤ ε) →
          ∀ u ∈ Icc (0 : ℝ) B,
            cStar * (1 - ϱ) ^ (N - 1) *
                Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) ≤
              G.obs (D N u (chainState D B G.e0 N)) ∧
            0 < cStar * (1 - ϱ) ^ (N - 1) *
                Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) := by
  obtain ⟨K, hKa, hKj⟩ := exists_coneConstants G hϱ0
  refine ⟨K.B, K.one_le_B, K.ω, K.ω_pos, K.ε, K.ε_pos, G.aStar * G.jStar / 4,
    by have := G.margin_ell; have := G.margin_obs; unfold GroundFamily.aStar GroundFamily.jStar
       positivity, rfl, ?_⟩
  intro N hN σ hσ hadj D hD u hu
  have h := K.positive_product_of_constants hϱ1 hN hσ hadj hD hu
  rw [hKa, hKj] at h
  exact h

/-- Exact-hypothesis wrapper of `L:raw-block-indexed-cone` with the standing
assumptions of Section `S:actual-raw-block-lower` (TeX lines 4--9): a NONZERO
covariance `Γ` from `H:homog` (`HomogCovariance`, `Γ ≠ 0`; both carried and
unused, since the lemma depends on `Γ` only through the ground family), the
ground family `G` of `S:compact-mean-family` for `V_s = m_R h_s` (supplied:
its construction is C16 and is not formalized, so the link of `G` to `Γ` is by
documentation), and `0 < ϱ < 1/2` (TeX line 234). -/
theorem indexed_cone_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd d)}
    (_hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0)
    (G : GroundFamily F) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ < 1 / 2) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ ω : ℝ, 0 < ω ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ cStar : ℝ, 0 < cStar ∧
      cStar = G.aStar * G.jStar / 4 ∧
      ∀ N : ℕ, 1 ≤ N → ∀ σ : ℕ → ℝ, (∀ m ≤ N, σ m ∈ paramI) →
        (∀ m < N, |σ (m + 1) - σ m| ≤ ω) →
        ∀ D : ℕ → ℝ → F →L[ℝ] F,
          (∀ m ≤ N, ∀ u ∈ Icc (0 : ℝ) B, ‖D m u - G.P (σ m) u‖ ≤ ε) →
          ∀ u ∈ Icc (0 : ℝ) B,
            cStar * (1 - ϱ) ^ (N - 1) *
                Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) ≤
              G.obs (D N u (chainState D B G.e0 N)) ∧
            0 < cStar * (1 - ϱ) ^ (N - 1) *
                Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) :=
  indexed_cone G hϱ0 hϱ1

/-! ### A scalar ground family (non-vacuity witness) -/

/-- A scalar ground family on `F = ℝ` (auxiliary to the Lean development: it
shows that the hypothesis structure `GroundFamily` is satisfiable, and it is
the counterexample carrier of the refutations): `P_σ(t) = e^t`, `e_σ = 1`,
`ℓ_σ = id`, `λ_σ = 1`, `e_0 = 1`, `O = id`, `d_0 = 1`; then `Q_σ = 0`. -/
def scalarFamily : GroundFamily ℝ where
  P := fun _ t => Real.exp t • ContinuousLinearMap.id ℝ ℝ
  e := fun _ => 1
  ell := fun _ => ContinuousLinearMap.id ℝ ℝ
  lam := fun _ => 1
  e0 := 1
  obs := ContinuousLinearMap.id ℝ ℝ
  d0 := 1
  lam_pos := fun _ _ => one_pos
  ell_e := fun _ _ => rfl
  P_Pi := fun _ _ t _ => by ext; simp
  Pi_P := fun _ _ t _ => by ext; simp
  d0_pos := one_pos
  normalized_complement := fun _ _ _ => ⟨0, fun _ _ t _ => by
    have h : ContinuousLinearMap.id ℝ ℝ - (ContinuousLinearMap.id ℝ ℝ).smulRight (1 : ℝ) = 0 := by
      ext; simp
    rw [h]; simp⟩
  e_cont := continuousOn_const
  ell_cont := continuousOn_const
  margin_ell := by
    have : Nonempty paramI := ⟨⟨0, by simp [paramI]⟩⟩
    simp
  margin_obs := by
    have : Nonempty paramI := ⟨⟨0, by simp [paramI]⟩⟩
    simp

/-- `a_* = 1` for `scalarFamily` (auxiliary: refutation data). -/
theorem scalarFamily_aStar : scalarFamily.aStar = 1 := by
  have : Nonempty paramI := ⟨⟨0, by simp [paramI]⟩⟩
  simp [GroundFamily.aStar, scalarFamily]

/-- `j_* = 1` for `scalarFamily` (auxiliary: refutation data). -/
theorem scalarFamily_jStar : scalarFamily.jStar = 1 := by
  have : Nonempty paramI := ⟨⟨0, by simp [paramI]⟩⟩
  simp [GroundFamily.jStar, scalarFamily]

end StratonovichHAMSecondMoment.IndexedCone
