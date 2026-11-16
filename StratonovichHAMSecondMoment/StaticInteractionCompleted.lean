module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`C:static-interaction` (Summable static interaction bounds) of
`notes/notes_stratonovich_ham_second_moment.tex` (main TeX file; line numbers at
revision 39f2597a; statement lines 3216-3262, proof 3264-3341) re-issued with
fewer supplied inputs, using wave items L8-h (`StaticPhaseCauchy`), L9-H3
(`ComplexPhaseScalar`) and L9-P (`PhaseContractions`, completed in `L9Completed`).

`IntervalScalar.static_interaction_paper` supplies five inputs: the identity
`I_σ^ε(h)(f,g) = ∑ σ^n Y_n`, the order bounds `‖Y_n‖ ≤ √e/(λh) (A√R)^n …`
(lines 3286-3292), the Gaussian parity (line 3293) and the two first-variance
bounds (lines 3275-3280).  This module proves:

1. The identity (`static_interaction_orders`): with `T` standing for
   `S_0(-h)`, a continuous linear map, `∑ σ^n Z_n` converges (proved from the
   order bounds) and `T (∑ σ^n Z_n) = ∑ σ^n T Z_n`; `Y_0 = (f,g)` follows from
   `Z_0 = S_0(h)(f,g)` and `S_0(-h) S_0(h) = 1`.  The definition of
   `I_σ^ε(h)` at lines 3220-3223 is `T (∑ σ^n Z_n)`, so the conclusion is about
   that map, not about a supplied series.
2. The order bounds of lines 3286-3292 from `E:all-static-phase-orders`, the
   free estimate `‖S_0(∓h)‖_λ ≤ √e` (lines 3273-3275) and the norm comparisons
   for `λh ≤ 1` (`transported_le`), with the TeX's constant
   `A_α = allOrdersA α = 400√2 e²/δ_{α/2}` instead of an arbitrary `A ≥ 0`.
3. `E:all-static-phase-orders` itself from the inputs of
   `StaticPhaseCauchy.static_phase_all_orders_step`, in which the circle bound
   `100 e^{2λh}` (the use of `L:fock-form` and `L:complex-phase` at lines
   3129-3132) is no longer supplied: it is proved (`circle_of_complex_phase`)
   by `ComplexPhaseScalar.complex_phase_paper` at `a = α/2`, `λ = n/h`, from
   the more primitive inputs of that lemma (`CPInputs`, `PropagatorBlock`) and
   `L:fock-form` in operator form (`FockSandwich`).
4. `E:independent-static-blocks` (`independent_static_blocks_operator_paper`):
   the per-block scalar step `m_{j+1} ≤ e^{λh_j}(1+𝓔_j) m_j` is no longer
   supplied; it is proved from the factorization `M_j = S_0(h_j) I_j`,
   `‖S_0(h_j)‖² ≤ e^{λh_j}` and the per-block interaction bound on phases
   adapted to the past (`hI`, the tensored form of `E:static-interaction`).

The section's class enters the wrappers as `PhaseContractions.PhaseCovariance`
(lines 2490-2493), with `R_α = SpectralMassIdentity.ralpha μ α` and
`D_Γ = PhaseContractions.dGam Γ α` (`E:phase-constants`, lines 2494-2501); only
`0 < α < 2` is used (also for `R_α, D_Γ ≥ 0`); the local finiteness of `μ`, `Γ` is carried.

Still supplied (named, not formalized here):
* `FockSandwich` (`E:fock-sandwich` of `L:fock-form`, lines 2972-2976, for the
  operator `A_ρ^{-1/2} B A_ρ^{-1/2}` on the cutoff Hilbert space).
  `FockForm.fock_form` proves the same bound in the Hermite coefficient model
  from `FockForm.FockColumn` (wave L9-H); identifying that model with a Hilbert
  space carrying `A_ρ = ρ² - Δ` is not formalized, and `FockColumn` itself is
  reserved for item K2 (its scalar core `E:phase-resolvent` is proved by
  `L9Completed.phase_contractions_paper_completed`).
* `CPInputs`: Crouzeix-Palencia `E:cp-input` (imported in the TeX, lines
  2739-2748) and the inverse-root integral of lines 2801-2826, the inputs of
  `ComplexPhaseScalar.complex_phase_paper`; `PropagatorBlock`: the
  identification of `M_z(h)` in `X_λ` with the weighted block map of lines
  2920-2931.
* the remaining inputs of `StaticPhaseCauchy.static_phase_all_orders_step`:
  entireness (lines 3134-3135), the coefficient identification via
  `L:finite-word-cutoff` with `‖z‖_{1/h} ≤ n‖z‖_{n/h}` (lines 3143-3154),
  `‖S_b(f,g)‖_{n/h} ≤ ‖(f,g)‖_{1/h}` (line 3155) and the two cutoff removals
  (lines 3168-3192, as convergence of norms);
* the free estimate `‖S_0(±h)‖_λ ≤ √e`, the group law `S_0(-h)S_0(h) = 1`,
  `Z_0 = S_0(h)(f,g)` and the two norm comparisons for `λh ≤ 1`
  (`‖Z_n‖_λ ≤ (λh)^{-1}‖Z_n‖_{1/h}`, `‖(f,g)‖_{1/h} ≤ ‖(f,g)‖_λ`; their
  multiplier form is `ComplexPhaseScalar.phase_weight_change`);
* Gaussian parity (line 3293; needs Gaussian chaos, D1) and the first-variance
  bounds of `P:static-phase-variance` (lines 3275-3280; not formalized);
* for the blocks, the per-block bound on adapted phases (density and
  tensoring with the independent past, lines 3332-3337; needs D1).

Model.  `E` (real Hilbert space) stands for `L²(Ω; X_λ)`; the
`L²(Ω; X_{1/h})` norms of the Duhamel phases are the real numbers `zn n`.
Narrower than the TeX: the conclusions concern the quantities named by the
inputs; uniformity in `ε` is that of the inputs.

Junk values: every real power has a positive base or is one of
`(√R)^n`, `(n!)^γ`, `t^{-1/2}` with `t > 0`; `R_α`, `D_Γ` use `toReal` of
finite ball masses; `δ_{α/2} > 0` and `1 - δ_{α/2} ≥ 3/4`; summability is proved,
never assumed through `tsum`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.IntervalScalar
public import StratonovichHAMSecondMoment.StaticPhaseCauchy
public import StratonovichHAMSecondMoment.ComplexPhaseScalar
public import StratonovichHAMSecondMoment.PhaseContractions

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real Finset Filter Topology MeasureTheory Set
open scoped Nat

namespace StratonovichHAMSecondMoment.StaticInteractionCompleted

open StratonovichHAMSecondMoment.StaticPhaseCauchy StratonovichHAMSecondMoment.ComplexPhaseScalar
open StratonovichHAMSecondMoment.IntervalScalar (staticE)
open StratonovichHAMSecondMoment.PhaseContractions (PhaseCovariance dGam)
open StratonovichHAMSecondMoment.SpectralMassIdentity (ralpha)
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-! ## The circle bound from `L:complex-phase` (main TeX lines 3129-3132) -/

/-- The coupling disc of `P:static-phase-all-orders` at order `n` (main TeX lines
3129-3132): `|z| ≤ δ_{α/2} λ^{2-α/2}/d'` for some `d' > 0` with `d' ≥ d_n`, at
`λ = n/h`. -/
def InDisc (n : ℕ) (alpha h R : ℝ) (z : ℂ) : Prop :=
  ∃ d' : ℝ, 0 < d' ∧ fockD n R ≤ d' ∧
    ‖z‖ ≤ deltaA (alpha / 2) * ((n : ℝ) / h) ^ (2 - alpha / 2) / d'

section Circle

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Supplied input (`L:fock-form` in operator form, `E:fock-sandwich`, main
TeX lines 2972-2976)**: `‖A_ρ^{-1/2} B A_ρ^{-1/2}‖ ≤ d ρ^{a-2}` for all
`ρ > 0`, with `A_ρ^{-1/2}` the inverse of the square root of `A_0 + ρ²`
(`ComplexPhaseScalar.invSqrtShift`).  This is `E:abstract-sandwich` of
`L:complex-phase` (lines 2755-2759).  At `B = B_{N,m,b}`, `d = d_N`,
`a = α/2` it is `L:fock-form`; `FockForm.fock_form` proves that bound in the
Hermite coefficient model from `FockForm.FockColumn`, not for this operator. -/
def FockSandwich (A0 B : H →L[ℂ] H) (d a : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ‖invSqrtShift A0 ρ * B * invSqrtShift A0 ρ‖ ≤ d * ρ ^ (a - 2)

/-- **Supplied input (the propagator identification of `L:complex-phase`, main
TeX lines 2920-2931 and 2948-2951)**: every bound for the weighted block map on
`H ⊕ H` built from `C_h(L)`, `F_h(L)`, `H_h(L)` and the root comparisons
`Q'^*`, `(Q'^{-1})^*` bounds the phase propagator `F_z = M_z(h)` in `X_λ` (the
two are conjugate by the isometry `(u,v) ↦ (u, A_λ^{-1/2} v)`). -/
def PropagatorBlock {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Fz : E →L[ℂ] E)
    (Cop Fop Hop Q' : H →L[ℂ] H) : Prop :=
  ∀ C : ℝ, 0 ≤ C → (∀ u v : H,
    √(‖Cop u + (Fop ∘L ContinuousLinearMap.adjoint Q') v‖ ^ 2 +
        ‖(-(ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Hop)) u +
          (ContinuousLinearMap.adjoint (Ring.inverse Q') ∘L Cop ∘L
            ContinuousLinearMap.adjoint Q') v‖ ^ 2) ≤ C * √(‖u‖ ^ 2 + ‖v‖ ^ 2)) → ‖Fz‖ ≤ C

/-- **Supplied input (the analytic inputs of `L:complex-phase`, main TeX lines
2739-2748 and 2801-2826)** on the coupling disc at order `n`, `λ = n/h`,
`a = α/2`, `L = A_0 - zB`: Crouzeix-Palencia `E:cp-input` for the three
functions `C_h, F_h, H_h` on the numerical range (`cpC`, `cpF`, `cpH`), and the
inverse-root integral `Q' - 1 = π⁻¹ ∫_0^∞ J(t) dt` with `J` a.e. strongly measurable on `(0, ∞)`
and `‖J(t)‖ ≤ (|z| d_n/(1-δ_a)) t^{-1/2}(λ²+t)^{(a-3)/2}` (`meas`, `bound`,
`rep`).  These are the hypotheses of `ComplexPhaseScalar.complex_phase_paper`
with `d = d_n`. -/
structure CPInputs (A0 B : H →L[ℂ] H) (n : ℕ) (alpha h R : ℝ) (Cop Fop Hop Q' : ℂ → H →L[ℂ] H)
    (J : ℂ → ℝ → H →L[ℂ] H) : Prop where
  cpC : ∀ z, InDisc n alpha h R z → ∀ M : ℝ, 0 ≤ M →
    (∀ w ∈ numRange (A0 - z • B), ‖phaseC h w‖ ≤ M) → ‖Cop z‖ ≤ (1 + √2) * M
  cpF : ∀ z, InDisc n alpha h R z → ∀ M : ℝ, 0 ≤ M →
    (∀ w ∈ numRange (A0 - z • B), ‖phaseF h ((n : ℝ) / h) w‖ ≤ M) → ‖Fop z‖ ≤ (1 + √2) * M
  cpH : ∀ z, InDisc n alpha h R z → ∀ M : ℝ, 0 ≤ M →
    (∀ w ∈ numRange (A0 - z • B), ‖phaseH h ((n : ℝ) / h) w‖ ≤ M) → ‖Hop z‖ ≤ (1 + √2) * M
  meas : ∀ z, InDisc n alpha h R z → AEStronglyMeasurable (J z) (volume.restrict (Ioi 0))
  bound : ∀ z, InDisc n alpha h R z → ∀ t ∈ Ioi (0 : ℝ),
    ‖J z t‖ ≤ ‖z‖ * fockD n R / (1 - deltaA (alpha / 2)) *
      (t ^ (-(1 / 2 : ℝ)) * (((n : ℝ) / h) ^ 2 + t) ^ ((alpha / 2 - 3) / 2))
  rep : ∀ z, InDisc n alpha h R z → Q' z - 1 = (1 / π) • ∫ t in Ioi (0 : ℝ), J z t

/-- **The circle bound of `P:static-phase-all-orders`** (main TeX lines
3129-3132): `L:fock-form` (as `FockSandwich` at `d_n`) and `L:complex-phase`
(proved by `ComplexPhaseScalar.complex_phase_paper` at `a = α/2`, `λ = n/h`,
`d = d'` from `CPInputs` and `PropagatorBlock`) give `‖M_z(h)‖ ≤ 100 e^{2λh}` on
`|z| ≤ δ_{α/2} λ^{2-α/2}/d'` for every `d' > 0`, `d' ≥ d_n`.  The conclusion is
the hypothesis `hcircle` of `StaticPhaseCauchy.static_phase_order_cutoff`. -/
theorem circle_of_complex_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : ℂ → E →L[ℂ] E) (A0 B : H →L[ℂ] H) (hA0 : A0.IsPositive) (hB : IsSelfAdjoint B)
    {n : ℕ} (hn : 1 ≤ n) {alpha h R : ℝ} (hα0 : 0 < alpha) (hα2 : alpha < 2) (hh : 0 < h)
    (hsand : FockSandwich A0 B (fockD n R) (alpha / 2))
    (Cop Fop Hop Q' : ℂ → H →L[ℂ] H) (J : ℂ → ℝ → H →L[ℂ] H)
    (hcp : CPInputs A0 B n alpha h R Cop Fop Hop Q' J)
    (hprop : ∀ z, InDisc n alpha h R z → PropagatorBlock (F z) (Cop z) (Fop z) (Hop z) (Q' z)) :
    ∀ d' : ℝ, 0 < d' → fockD n R ≤ d' → ∀ z : ℂ,
      ‖z‖ ≤ deltaA (alpha / 2) * ((n : ℝ) / h) ^ (2 - alpha / 2) / d' →
        ‖F z‖ ≤ 100 * Real.exp (2 * ((n : ℝ) / h) * h) := by
  intro d' hd' hdd z hz
  have hD : InDisc n alpha h R z := ⟨d', hd', hdd, hz⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlam : (0 : ℝ) < n / h := by positivity
  have hsand' : ∀ ρ > (0 : ℝ),
      ‖invSqrtShift A0 ρ * B * invSqrtShift A0 ρ‖ ≤ d' * ρ ^ (alpha / 2 - 2) := fun ρ hρ =>
    (hsand ρ hρ).trans (mul_le_mul_of_nonneg_right hdd (Real.rpow_nonneg hρ.le _))
  have hδ : 0 < 1 - deltaA (alpha / 2) := by linarith [one_sub_deltaA_ge (alpha / 2)]
  have hJ' : ∀ t ∈ Ioi (0 : ℝ), ‖J z t‖ ≤ ‖z‖ * d' / (1 - deltaA (alpha / 2)) *
      (t ^ (-(1 / 2 : ℝ)) * (((n : ℝ) / h) ^ 2 + t) ^ ((alpha / 2 - 3) / 2)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    refine (hcp.bound z hD t ht).trans ?_
    have hX : 0 ≤ t ^ (-(1 / 2 : ℝ)) * (((n : ℝ) / h) ^ 2 + t) ^ ((alpha / 2 - 3) / 2) := by
      positivity
    gcongr
  obtain ⟨-, -, -, -, -, -, -, -, hblock⟩ :=
    complex_phase_paper A0 B hA0 hB (a := alpha / 2) (d := d') (by linarith) (by linarith) hd'
      hsand' hlam hz hh.le (Cop z) (Fop z) (Hop z) (hcp.cpC z hD) (hcp.cpF z hD) (hcp.cpH z hD)
      (Q' z) (J z) (hcp.meas z hD) hJ' (hcp.rep z hD)
  have e : 2 * ((n : ℝ) / h * h) = 2 * ((n : ℝ) / h) * h := by ring
  have hF := hprop z hD _ (by positivity) hblock
  rwa [e] at hF

end Circle

/-! ## `E:all-static-phase-orders` without the circle input -/

/-- **`E:all-static-phase-orders`** (main TeX lines 3098-3105, proof 3127-3192)
with the circle bound proved (`circle_of_complex_phase`) at every Gaussian cutoff
`m` and band `b`: for `0 < α < 2`, `h > 0`, `n ≥ 1`,
`z ≤ (A_α √R)^n h^{(4-α)n/2}/(n!)^{(3-α)/2} N1` with `A_α = allOrdersA α`.
Supplied: `FockSandwich`, `CPInputs`, `PropagatorBlock` at each cutoff, and the
inputs `hentire`, `hz`, `hv`, `hband`, `hgauss` of
`StaticPhaseCauchy.static_phase_all_orders_step` (documented there). -/
theorem static_phase_all_orders_cp (Ec : ℕ → ℕ → Type*) [∀ m b, NormedAddCommGroup (Ec m b)]
    [∀ m b, NormedSpace ℂ (Ec m b)] [∀ m b, CompleteSpace (Ec m b)]
    (Hs : ℕ → ℕ → Type*) [∀ m b, NormedAddCommGroup (Hs m b)]
    [∀ m b, InnerProductSpace ℂ (Hs m b)] [∀ m b, CompleteSpace (Hs m b)]
    (F : ∀ m b, ℂ → Ec m b →L[ℂ] Ec m b) (v : ∀ m b, Ec m b) (zc : ℕ → ℕ → ℝ) (zm : ℕ → ℝ)
    {n : ℕ} (hn : 1 ≤ n) {alpha h R z N1 : ℝ} (hα0 : 0 < alpha) (hα2 : alpha < 2) (hh : 0 < h)
    (A0 B : ∀ m b, Hs m b →L[ℂ] Hs m b) (hA0 : ∀ m b, (A0 m b).IsPositive)
    (hB : ∀ m b, IsSelfAdjoint (B m b))
    (hsand : ∀ m b, FockSandwich (A0 m b) (B m b) (fockD n R) (alpha / 2))
    (Cop Fop Hop Q' : ∀ m b, ℂ → Hs m b →L[ℂ] Hs m b) (J : ∀ m b, ℂ → ℝ → Hs m b →L[ℂ] Hs m b)
    (hcp : ∀ m b, CPInputs (A0 m b) (B m b) n alpha h R (Cop m b) (Fop m b) (Hop m b) (Q' m b)
      (J m b))
    (hprop : ∀ m b z, InDisc n alpha h R z →
      PropagatorBlock (F m b z) (Cop m b z) (Fop m b z) (Hop m b z) (Q' m b z))
    (hentire : ∀ m b, Differentiable ℂ (F m b))
    (hz : ∀ m b, zc m b ≤ n * ‖taylorCoeff (F m b) n (v m b)‖) (hv : ∀ m b, ‖v m b‖ ≤ N1)
    (hband : ∀ m, Tendsto (zc m) atTop (𝓝 (zm m))) (hgauss : Tendsto zm atTop (𝓝 z)) :
    z ≤ (allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * N1 :=
  static_phase_all_orders_step Ec F v zc zm hn (by linarith) hh
    (deltaA_pos (a := alpha / 2) (by linarith)) hentire
    (fun m b => circle_of_complex_phase (F m b) (A0 m b) (B m b) (hA0 m b) (hB m b) hn hα0 hα2 hh
      (hsand m b) (Cop m b) (Fop m b) (Hop m b) (Q' m b) (J m b) (hcp m b) (hprop m b))
    hz hv hband hgauss

/-! ## `E:static-interaction` -/

/-- Step of `C:static-interaction` (main TeX lines 3273-3292): the transported
order bound.  For `0 ≤ a` and `0 < λh`: if `‖T‖ ≤ √e` (free estimate),
`‖x‖ ≤ (λh)⁻¹ z` (norm comparison), `z ≤ a N1` (an order bound) and `N1 ≤ N`, then
`‖T x‖ ≤ √e/(λh) · a · N`. -/
theorem transported_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : E →L[ℝ] E)
    (hT : ‖T‖ ≤ √(Real.exp 1)) {z a N1 N lh : ℝ} (ha : 0 ≤ a) (hlh : 0 < lh) (x : E)
    (hcmp : ‖x‖ ≤ lh⁻¹ * z) (hz : z ≤ a * N1) (hN : N1 ≤ N) :
    ‖T x‖ ≤ √(Real.exp 1) / lh * a * N := by
  have hi : 0 ≤ lh⁻¹ := inv_nonneg.2 hlh.le
  calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    _ ≤ √(Real.exp 1) * (lh⁻¹ * (a * N)) := by
        gcongr
        exact hcmp.trans (mul_le_mul_of_nonneg_left (hz.trans
          (mul_le_mul_of_nonneg_left hN ha)) hi)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- **`E:static-interaction` from `E:all-static-phase-orders`** (main TeX lines
3216-3240, proof 3264-3311).  In a complete real inner product space `E`
standing for `L²(Ω; X_λ)`, let `T = S_0(-h)`, `S = S_0(h)` with
`‖T‖, ‖S‖ ≤ √e` (`hT`, `hS`; lines 3273-3275) and `T (S x) = x` (`hTS`), let
`f0 = (f,g)`, `Z n` the Duhamel phases with `Z 0 = S f0` (`hZ0`) and `zn n` their
`L²(Ω; X_{1/h})` norms.  Supplied: the comparisons `‖Z n‖ ≤ (λh)⁻¹ zn n`
(`hcmp`) and `N1 ≤ ‖f0‖` (`hN1`, `N1 = ‖(f,g)‖_{1/h}`), the order bounds
`horders` (`E:all-static-phase-orders`, proved under its inputs by
`static_phase_all_orders_cp`), the parity `hodd` (line 3293) and the
first-variance bounds `hborn`, `hmean` (lines 3275-3280) for `Y_n = T (Z n)`.
Conclusion: `∑ σ^n Z_n` converges, `I = T (∑ σ^n Z_n) = ∑ σ^n Y_n`, and
`‖I‖² ≤ (1 + 𝓔(h,σ,λ)) ‖f0‖²` with the TeX's `A_α`. -/
theorem static_interaction_orders {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T S : E →L[ℝ] E) (f0 : E) (Z : ℕ → E) (zn : ℕ → ℝ)
    {alpha R D h lam σ N1 : ℝ} (hα0 : 0 < alpha) (hα2 : alpha < 2) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlam : 0 < lam) (hh : 0 < h) (hlh : lam * h ≤ 1)
    (hT : ‖T‖ ≤ √(Real.exp 1)) (hS : ‖S‖ ≤ √(Real.exp 1)) (hTS : ∀ x, T (S x) = x)
    (hZ0 : Z 0 = S f0) (hcmp : ∀ n, 1 ≤ n → ‖Z n‖ ≤ (lam * h)⁻¹ * zn n) (hN1 : N1 ≤ ‖f0‖)
    (horders : ∀ n, 1 ≤ n → zn n ≤ (allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * N1)
    (hodd : ∀ r s, Odd (r + s) → inner ℝ (T (Z r)) (T (Z s)) = 0)
    (hborn : ‖T (Z 1)‖ ^ 2 ≤
      Real.exp 1 * (R * h ^ 2 * lam ^ (alpha - 2) * (1 + lam ^ 2 * h ^ 2) ^ 2 * ‖f0‖ ^ 2))
    (hmean : |inner ℝ f0 (T (Z 2))| ≤ ‖f0‖ * (√(Real.exp 1) * (D * (1 + lam ^ 2 * h ^ 2) *
      h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * ‖f0‖))) :
    Summable (fun n => σ ^ n • Z n) ∧
      T (∑' n, σ ^ n • Z n) = ∑' n, σ ^ n • T (Z n) ∧
      ‖T (∑' n, σ ^ n • Z n)‖ ^ 2 ≤
        (1 + staticE alpha (allOrdersA alpha) R D h σ lam) * ‖f0‖ ^ 2 := by
  have hlh0 : 0 < lam * h := mul_pos hlam hh
  have hA : 0 ≤ allOrdersA alpha := (allOrdersA_pos (by linarith)).le
  have hcoef : ∀ n : ℕ, 0 ≤ (allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) := fun n => by positivity
  have hY0 : T (Z 0) = f0 := by rw [hZ0, hTS]
  -- the transported order bounds (lines 3286-3292)
  have hY : ∀ n, 1 ≤ n → ‖T (Z n)‖ ≤ √(Real.exp 1) / (lam * h) *
      ((allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
        (n ! : ℝ) ^ ((3 - alpha) / 2)) * ‖f0‖ := fun n hn =>
    transported_le T hT (hcoef n) hlh0 (Z n) (hcmp n hn) (horders n hn) hN1
  -- summability of the Duhamel series in `X_λ`
  have hK : 1 ≤ (lam * h)⁻¹ := by rw [le_inv_comm₀ (by norm_num) hlh0]; simpa using hlh
  have hZ0' : ‖Z 0‖ ≤ √(Real.exp 1) * ((lam * h)⁻¹ * ‖f0‖) := by
    rw [hZ0]
    calc ‖S f0‖ ≤ ‖S‖ * ‖f0‖ := S.le_opNorm f0
      _ ≤ √(Real.exp 1) * (1 * ‖f0‖) := by rw [one_mul]; gcongr
      _ ≤ _ := by gcongr
  have hZ' : ∀ n, 1 ≤ n → ‖Z n‖ ≤ (allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * ((lam * h)⁻¹ * ‖f0‖) := by
    intro n hn
    have hi : 0 ≤ (lam * h)⁻¹ := inv_nonneg.2 hlh0.le
    calc ‖Z n‖ ≤ (lam * h)⁻¹ * zn n := hcmp n hn
      _ ≤ (lam * h)⁻¹ * ((allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
            (n ! : ℝ) ^ ((3 - alpha) / 2) * ‖f0‖) :=
          mul_le_mul_of_nonneg_left ((horders n hn).trans
            (mul_le_mul_of_nonneg_left hN1 (hcoef n))) hi
      _ = _ := by ring
  obtain ⟨-, hsum, -⟩ := all_static_phase_sum_step (σ := σ) Z hα0.le hα2.le hA hR hh hZ0' hZ'
  -- the identification `I = ∑ σ^n Y_n`
  have hid : T (∑' n, σ ^ n • Z n) = ∑' n, σ ^ n • T (Z n) := by
    rw [T.map_tsum hsum]
    simp only [map_smul]
  refine ⟨hsum, hid, ?_⟩
  have hmean' : |inner ℝ (T (Z 0)) (T (Z 2))| ≤ ‖f0‖ * (√(Real.exp 1) * (D *
      (1 + lam ^ 2 * h ^ 2) * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * ‖f0‖)) := by
    rw [hY0]; exact hmean
  obtain ⟨-, hb⟩ := IntervalScalar.static_interaction_step (σ := σ) (fun n => T (Z n)) hα0 hα2
    hA hR hD hlam hh hlh (norm_nonneg f0) (by rw [hY0]) hY hodd hborn hmean'
  rw [hid]
  exact hb

/-- Auxiliary (Lean route): under the section's class, `R_α ≥ 0` and
`D_Γ ≥ 0` (main TeX lines 2494-2501). -/
theorem constants_nonneg {alpha : ℝ} {Γ μ : Measure (Rd 3)} (hcov : PhaseCovariance alpha Γ μ) :
    0 ≤ ralpha μ alpha ∧ 0 ≤ dGam Γ alpha :=
  ⟨IntervalScalar.ralpha_nonneg μ hcov.alpha_pos hcov.alpha_lt_two,
    IntervalScalar.dgamma_nonneg Γ hcov.alpha_lt_two⟩

/-- **`C:static-interaction`, `E:static-interaction`, with the section's class
and nothing about the phase orders supplied beyond the primitive inputs** (main
TeX lines 3216-3240, proof 3264-3311; orders from lines 3098-3192).  Under
`PhaseCovariance α Γ μ` (lines 2490-2493), `R_α = ralpha μ α`,
`D_Γ = dGam Γ α`, `λ, h > 0`, `λh ≤ 1`: the hypotheses of
`static_interaction_orders` with `horders` replaced, for every order `n ≥ 1`,
by the inputs of `static_phase_all_orders_cp` (Hilbert and Banach spaces
`Hs n m b`, `Ec n m b` for the cutoffs `m`, `b` at `λ = n/h`, with the cutoff
removals converging to `zn n`).  Conclusion: `∑ σ^n Z_n` converges,
`I_σ^ε(h)(f,g) = T (∑ σ^n Z_n) = ∑ σ^n T Z_n`, and
`‖I_σ^ε(h)(f,g)‖² ≤ (1 + 𝓔(h,σ,λ)) ‖(f,g)‖²` with `A_α = allOrdersA α`.
Used from `hcov`: only `0 < α < 2` (also for `R_α, D_Γ ≥ 0`); local finiteness and the
other fields are carried, unused. -/
theorem static_interaction_completed_paper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ec : ℕ → ℕ → ℕ → Type*) [∀ n m b, NormedAddCommGroup (Ec n m b)]
    [∀ n m b, NormedSpace ℂ (Ec n m b)] [∀ n m b, CompleteSpace (Ec n m b)]
    (Hs : ℕ → ℕ → ℕ → Type*) [∀ n m b, NormedAddCommGroup (Hs n m b)]
    [∀ n m b, InnerProductSpace ℂ (Hs n m b)] [∀ n m b, CompleteSpace (Hs n m b)]
    {alpha h lam σ N1 : ℝ} {Γ μ : Measure (Rd 3)} (hcov : PhaseCovariance alpha Γ μ)
    (hlam : 0 < lam) (hh : 0 < h) (hlh : lam * h ≤ 1)
    (T S : E →L[ℝ] E) (f0 : E) (Z : ℕ → E) (zn : ℕ → ℝ)
    (hT : ‖T‖ ≤ √(Real.exp 1)) (hS : ‖S‖ ≤ √(Real.exp 1)) (hTS : ∀ x, T (S x) = x)
    (hZ0 : Z 0 = S f0) (hcmp : ∀ n, 1 ≤ n → ‖Z n‖ ≤ (lam * h)⁻¹ * zn n) (hN1 : N1 ≤ ‖f0‖)
    (F : ∀ n m b, ℂ → Ec n m b →L[ℂ] Ec n m b) (v : ∀ n m b, Ec n m b)
    (zc : ℕ → ℕ → ℕ → ℝ) (zm : ℕ → ℕ → ℝ)
    (A0 B : ∀ n m b, Hs n m b →L[ℂ] Hs n m b) (hA0 : ∀ n m b, (A0 n m b).IsPositive)
    (hB : ∀ n m b, IsSelfAdjoint (B n m b))
    (hsand : ∀ n, 1 ≤ n → ∀ m b,
      FockSandwich (A0 n m b) (B n m b) (fockD n (ralpha μ alpha)) (alpha / 2))
    (Cop Fop Hop Q' : ∀ n m b, ℂ → Hs n m b →L[ℂ] Hs n m b)
    (J : ∀ n m b, ℂ → ℝ → Hs n m b →L[ℂ] Hs n m b)
    (hcp : ∀ n, 1 ≤ n → ∀ m b, CPInputs (A0 n m b) (B n m b) n alpha h (ralpha μ alpha)
      (Cop n m b) (Fop n m b) (Hop n m b) (Q' n m b) (J n m b))
    (hprop : ∀ n, 1 ≤ n → ∀ m b z, InDisc n alpha h (ralpha μ alpha) z →
      PropagatorBlock (F n m b z) (Cop n m b z) (Fop n m b z) (Hop n m b z) (Q' n m b z))
    (hentire : ∀ n, 1 ≤ n → ∀ m b, Differentiable ℂ (F n m b))
    (hz : ∀ n, 1 ≤ n → ∀ m b, zc n m b ≤ n * ‖taylorCoeff (F n m b) n (v n m b)‖)
    (hv : ∀ n, 1 ≤ n → ∀ m b, ‖v n m b‖ ≤ N1)
    (hband : ∀ n, 1 ≤ n → ∀ m, Tendsto (zc n m) atTop (𝓝 (zm n m)))
    (hgauss : ∀ n, 1 ≤ n → Tendsto (zm n) atTop (𝓝 (zn n)))
    (hodd : ∀ r s, Odd (r + s) → inner ℝ (T (Z r)) (T (Z s)) = 0)
    (hborn : ‖T (Z 1)‖ ^ 2 ≤ Real.exp 1 * (ralpha μ alpha * h ^ 2 * lam ^ (alpha - 2) *
      (1 + lam ^ 2 * h ^ 2) ^ 2 * ‖f0‖ ^ 2))
    (hmean : |inner ℝ f0 (T (Z 2))| ≤ ‖f0‖ * (√(Real.exp 1) * (dGam Γ alpha *
      (1 + lam ^ 2 * h ^ 2) * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * ‖f0‖))) :
    Summable (fun n => σ ^ n • Z n) ∧
      T (∑' n, σ ^ n • Z n) = ∑' n, σ ^ n • T (Z n) ∧
      ‖T (∑' n, σ ^ n • Z n)‖ ^ 2 ≤
        (1 + staticE alpha (allOrdersA alpha) (ralpha μ alpha) (dGam Γ alpha) h σ lam) *
          ‖f0‖ ^ 2 := by
  obtain ⟨hR, hD⟩ := constants_nonneg hcov
  have horders : ∀ n, 1 ≤ n → zn n ≤ (allOrdersA alpha * √(ralpha μ alpha)) ^ n *
      h ^ ((4 - alpha) * n / 2) / (n ! : ℝ) ^ ((3 - alpha) / 2) * N1 := fun n hn =>
    static_phase_all_orders_cp (Ec n) (Hs n) (F n) (v n) (zc n) (zm n) hn hcov.alpha_pos
      hcov.alpha_lt_two hh (A0 n) (B n) (hA0 n) (hB n) (hsand n hn) (Cop n) (Fop n) (Hop n)
      (Q' n) (J n) (hcp n hn) (hprop n hn) (hentire n hn) (hz n hn) (hv n hn) (hband n hn)
      (hgauss n hn)
  exact static_interaction_orders T S f0 Z zn hcov.alpha_pos hcov.alpha_lt_two hR hD hlam hh
    hlh hT hS hTS hZ0 hcmp hN1 horders hodd hborn hmean

/-! ## `E:independent-static-blocks` -/

/-- The block product `M_{k-1} ⋯ M_0 x` with `M_j = S_j ∘ I_j` (main TeX lines
3247-3256 and 3332-3334; indices start at `0`). -/
def blockIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S I : ℕ → E →L[ℝ] E) :
    ℕ → E → E
  | 0, x => x
  | k + 1, x => S k (I k (blockIter S I k x))

/-- **Step of `C:static-interaction`, `E:independent-static-blocks`, operator
form** (main TeX lines 3332-3339).  In a real normed space `E` standing for
`L²(Ω; X_λ)` on the product of the block probability spaces, let `P j` be the
phases adapted to the first `j` fields (independent of field `j`), with
`P 0 x`, and `M_j = S_j ∘ I_j` preserving adaptation (`hadapt`).  If
`‖S_j y‖² ≤ e^{ℓ_j}‖y‖²` (free evolution) and `‖I_j y‖² ≤ (1 + E_j)‖y‖²` for
adapted `y` (`hI`: the per-block interaction bound tensored with the
independent past, supplied) with `E_j ≥ 0`, then
`‖M_{K-1} ⋯ M_0 x‖² ≤ exp(∑ ℓ_j + ∑ E_j) ‖x‖²`.  The scalar step
`m_{j+1} ≤ e^{ℓ_j}(1+E_j) m_j` of `IntervalScalar.independent_static_blocks_paper`
is proved here. -/
theorem independent_static_blocks_operator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℕ) (S I : ℕ → E →L[ℝ] E) (lh Eb : ℕ → ℝ) (P : ℕ → E → Prop) (x : E)
    (hE : ∀ j, 0 ≤ Eb j) (hP0 : P 0 x)
    (hadapt : ∀ j y, j < K → P j y → P (j + 1) (S j (I j y)))
    (hS : ∀ j, j < K → ∀ y, ‖S j y‖ ^ 2 ≤ Real.exp (lh j) * ‖y‖ ^ 2)
    (hI : ∀ j, j < K → ∀ y, P j y → ‖I j y‖ ^ 2 ≤ (1 + Eb j) * ‖y‖ ^ 2) :
    ‖blockIter S I K x‖ ^ 2 ≤
      Real.exp (∑ j ∈ range K, lh j + ∑ j ∈ range K, Eb j) * ‖x‖ ^ 2 := by
  have hPk : ∀ k, k ≤ K → P k (blockIter S I k x) := by
    intro k
    induction k with
    | zero => intro _; exact hP0
    | succ k ih => intro hk; exact hadapt k _ (by omega) (ih (by omega))
  have hstep : ∀ j, j < K → ‖blockIter S I (j + 1) x‖ ^ 2 ≤
      Real.exp (lh j) * (1 + Eb j) * ‖blockIter S I j x‖ ^ 2 := by
    intro j hj
    show ‖S j (I j (blockIter S I j x))‖ ^ 2 ≤ _
    calc ‖S j (I j (blockIter S I j x))‖ ^ 2
        ≤ Real.exp (lh j) * ‖I j (blockIter S I j x)‖ ^ 2 := hS j hj _
      _ ≤ Real.exp (lh j) * ((1 + Eb j) * ‖blockIter S I j x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hI j hj _ (hPk j hj.le)) (Real.exp_pos _).le
      _ = _ := by ring
  have := IntervalScalar.independent_blocks_scalar K (fun k => ‖blockIter S I k x‖ ^ 2) lh Eb
    hE (sq_nonneg _) hstep
  simpa [blockIter] using this

/-- **`C:static-interaction`, `E:independent-static-blocks`** (main TeX lines
3247-3256, proof 3332-3339) under the section's class `PhaseCovariance α Γ μ`,
with `R_α = ralpha μ α`, `D_Γ = dGam Γ α`, `λ > 0`, `h_j > 0`: for blocks
`M_j = S_0(h_j) I_j` with `‖S_0(h_j) y‖² ≤ e^{λh_j}‖y‖²` (`hS`, free estimate)
and the supplied per-block bound `‖I_j y‖² ≤ (1 + 𝓔(h_j,σ_j,λ))‖y‖²` on phases
adapted to the past (`hI`, `E:static-interaction` tensored with the independent
past, lines 3333-3337), `‖M_{K-1} ⋯ M_0 (f,g)‖² ≤
exp{λ ∑ h_j + ∑ 𝓔(h_j,σ_j,λ)} ‖(f,g)‖²`.  Used from `hcov`: only `0 < α < 2`
(local finiteness carried, unused); `_hlh` (`λh_j ≤ 1`, which `hI` needs in the TeX) is carried,
not used. -/
theorem independent_static_blocks_operator_paper {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {alpha lam : ℝ} {Γ μ : Measure (Rd 3)} (hcov : PhaseCovariance alpha Γ μ)
    (K : ℕ) (h σ : ℕ → ℝ) (hlam : 0 < lam) (hh : ∀ j, 0 < h j) (_hlh : ∀ j, lam * h j ≤ 1)
    (S I : ℕ → E →L[ℝ] E) (P : ℕ → E → Prop) (x : E) (hP0 : P 0 x)
    (hadapt : ∀ j y, j < K → P j y → P (j + 1) (S j (I j y)))
    (hS : ∀ j, j < K → ∀ y, ‖S j y‖ ^ 2 ≤ Real.exp (lam * h j) * ‖y‖ ^ 2)
    (hI : ∀ j, j < K → ∀ y, P j y → ‖I j y‖ ^ 2 ≤
      (1 + staticE alpha (allOrdersA alpha) (ralpha μ alpha) (dGam Γ alpha) (h j) (σ j) lam) *
        ‖y‖ ^ 2) :
    ‖blockIter S I K x‖ ^ 2 ≤ Real.exp (lam * ∑ j ∈ range K, h j + ∑ j ∈ range K,
      staticE alpha (allOrdersA alpha) (ralpha μ alpha) (dGam Γ alpha) (h j) (σ j) lam) *
        ‖x‖ ^ 2 := by
  obtain ⟨hR, hD⟩ := constants_nonneg hcov
  have := independent_static_blocks_operator K S I (fun j => lam * h j)
    (fun j => staticE alpha (allOrdersA alpha) (ralpha μ alpha) (dGam Γ alpha) (h j) (σ j) lam)
    P x (fun j => IntervalScalar.staticE_nonneg hcov.alpha_lt_two hR hD hlam (hh j)) hP0 hadapt
    hS hI
  simpa [mul_sum] using this

end StratonovichHAMSecondMoment.StaticInteractionCompleted
