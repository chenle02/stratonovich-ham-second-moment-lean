module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-E3, part 3: `E:homogeneous-envelope` (`P:envelope`, main TeX lines 2352-2394),
`E:theta-envelope` and the diagram half of `E:crude-corrected` (`L:crude-corrected`, 1970-2041)
in `d = 3` for the Green-smoothed kernels `G_{s,η} = p_η * G_s`
(`smoothedGreen (waveGreen 3) s η`), uniformly in the Green-smoothing width `η > 0` and the noise
width `ε > 0`, at revision edf7085f (book 1.1.3); with the frozen `PairingEnvelopeTarget` as a
hypothesis (`hPE`), as item E does in `d = 1, 2`.

Formalized: `smoothDensity_three` (the `d = 3` smoothed Green measures satisfy
`PairingSmoothedNorms.SmoothDensity` with the density `GreenSmoothed3.green3s`, finite, so the
bridge `PairingBridge.diagram_le_pairingIntegral` applies); the generic `kernelHyp_damp`,
`norms_le_homog`, `diagram_le_homog` for any `SmoothDensity`; and
`homogeneous_envelope_diagrams_three`, `theta_envelope_diagrams_three`,
`crude_corrected_diagrams_three`, with constants independent of `η` and `ε` (`K = Khom α₀ μ`,
the same constant as in `d = 1, 2`).

Not formalized (L17 decision 5): the limit `η ↓ 0`.  It is the stochastic `L²` limit of the
TeX (the smoothed kernels converge to `G_s` only weakly; `waveGreen 3 s` has no density), so the
moment sentences through `DiagramModel.MixedMoment`, whose diagrams are those of the unsmoothed
`waveGreen d`, are not stated in `d = 3` (no `_paper` versions here).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.GreenSmoothed3
public import StratonovichHAMSecondMoment.PairingSmoothedNorms
public import StratonovichHAMSecondMoment.CrudeCorrected

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.EnvelopeD3

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (smoothedGreen)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps)
open PairingInterface
open PairingBridge
open PairingSmoothedNorms
open HomogeneousEnvelope (Khom Khom_pos prodP_const_le)
open GreenSmoothed3

variable {d : ℕ}

/-- The Green-smoothed `d = 3` wave kernels form a `SmoothDensity` (`η > 0`). -/
theorem smoothDensity_three {η : ℝ} (hη : 0 < η) :
    SmoothDensity 3 (fun s => smoothedGreen (waveGreen 3) s η) η (green3s η) :=
  ⟨Or.inr (Or.inr rfl), hη.le, measurable_green3s η, green3s_ne_top hη,
    smoothedGreen_three_eq hη, fun _ hs => smoothedGreen_three_mass η hs,
    fun _ hs ξ => charFun_smoothedGreen_three hη.le hs ξ⟩

section Homog

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
variable {G : ℝ → Measure (Rd d)} {η : ℝ} {g : Kernel d} (hgd : SmoothDensity d G η g)
  (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε)
include hgd hH hε

theorem kernelHyp_damp {θ : ℝ} (hθ : 0 < θ) {α : Type*} [DecidableEq α] (dg : TwoChain α) :
    KernelHyp α₀ dg (fun _ => smoothEdge hH hε) (fun _ => damp θ g) := by
  refine ⟨fun _ _ => hgd.measurable_damp θ, fun _ _ => ?_, fun _ _ _ _ => ?_,
    fun _ _ _ _ => ?_⟩
  · rw [N0_damp hgd hθ]; exact ENNReal.ofReal_lt_top
  · exact lt_of_le_of_lt (N1_damp_le hgd hH hε hθ) ENNReal.ofReal_lt_top
  · have h := lt_of_le_of_lt (N2_damp_sq_le hgd hH hε hθ) ENNReal.ofReal_lt_top
    refine lt_top_iff_ne_top.2 fun htop => ?_
    rw [htop] at h
    simp at h

theorem norms_le_homog {θ : ℝ} (hθ : 0 < θ) :
    N0 (damp θ g) * (2 * N1 α₀ (smoothEdge hH hε) (damp θ g)) ≤
        ENNReal.ofReal (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ∧
      N2 α₀ (smoothEdge hH hε) (damp θ g) ^ 2 ≤
        ENNReal.ofReal (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) := by
  have hI := MaskedSpectralGrowth.spectralHomogeneous_of_homog hH
  have hβ : 0 < θ ^ (-(4 - alpha - α₀)) := Real.rpow_pos_of_pos hθ _
  constructor
  · rw [N0_damp hgd hθ]
    calc ENNReal.ofReal (θ ^ (-(2 : ℝ))) * (2 * N1 α₀ (smoothEdge hH hε) (damp θ g))
        ≤ ENNReal.ofReal (θ ^ (-(2 : ℝ))) * (2 * ENNReal.ofReal (DampedNorms.N1 α₀ θ μ)) := by
          gcongr; exact N1_damp_le hgd hH hε hθ
      _ = ENNReal.ofReal (2 * DampedNorms.N1 α₀ 1 μ * θ ^ (-(4 - alpha - α₀))) := by
          rw [DampedNormsHomog.N1_scaling hI α₀ θ hθ, ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : θ ^ (-(2 : ℝ)) * θ ^ (alpha + α₀ - 2) = θ ^ (-(4 - alpha - α₀)) := by
            rw [← Real.rpow_add hθ]; ring_nf
          rw [← this]; ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hβ.le)
          exact (le_max_left _ _).trans (le_max_left _ _)
  · refine (N2_damp_sq_le hgd hH hε hθ).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [DampedNormsHomog.N2sq_scaling hH θ hθ, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hβ.le
    exact (le_max_right _ _).trans (le_max_left _ _)

/-- `J_{m,n,D}(t) ≤ K^k e^{2θt} θ^{-βk}` for the smoothed kernels, `m + n = 2k`, `θ > 0`. -/
theorem diagram_le_homog {m n k : ℕ} (hPE : PairingEnvelopeTarget d (Fin (m + n)))
    (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {t θ : ℝ}
    (ht : 0 < t) (hθ : 0 < θ) :
    diagram G (covEps Γ ε) α₀ m n D t ≤
      ENNReal.ofReal (Khom α₀ μ ^ k * Real.exp (2 * θ * t) *
        θ ^ (-((4 - alpha - α₀) * k))) := by
  obtain ⟨h1, h2⟩ := norms_le_homog hgd hH hε hθ
  have henv : env α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε) (fun _ => damp θ g) ≤
      ENNReal.ofReal (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ^ k := by
    refine iSup_le fun A => ?_
    have := prodP_const_le α₀ (smoothEdge hH hε) (damp θ g) A h1 h2
    rwa [card_D_m4Chain hD hmn] at this
  calc diagram G (covEps Γ ε) α₀ m n D t
      ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) *
          pairingIntegral α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε) (fun _ => damp θ g) :=
        diagram_le_pairingIntegral hH hε G g hgd.meas hgd.fin hgd.eq hD ht hθ.le
    _ ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) *
          env α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε) (fun _ => damp θ g) := by
        gcongr
        exact hPE α₀ hH.alpha0_pos hH.alpha0_lt_one _ _ _ (m4Chain_wf hD)
          (kernelHyp_damp hgd hH hε hθ _)
    _ ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) *
          ENNReal.ofReal (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ^ k := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity [Khom_pos α₀ μ]),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        rw [mul_pow, ← Real.rpow_natCast (θ ^ (-(4 - alpha - α₀))), ← Real.rpow_mul hθ.le]
        ring_nf

end Homog

/-- **`E:homogeneous-envelope` in `d = 3`** for the Green-smoothed kernels (`P:envelope`, Step 1,
TeX lines 2352-2394 at revision edf7085f (book 1.1.3)), with the frozen `PairingEnvelopeTarget`
as a hypothesis: one `K > 0` serves every Green-smoothing width `η > 0` and noise width `ε > 0`:
`Σ_{D ∈ Π} J^{(η)}_{m,n,D}(t) ≤ P_k K^k e^{2θt} θ^{-βk}` for `m + n = 2k ≥ 2`, `θ, t > 0`. -/
theorem homogeneous_envelope_diagrams_three {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha α₀ Γ μ) (hPE : ∀ N : ℕ, PairingEnvelopeTarget 3 (Fin N)) :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k →
      ∀ t θ : ℝ, 0 < t → 0 < θ →
        ∑ D ∈ Pi2 m n, diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ m n D t ≤
          ENNReal.ofReal ((Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
            θ ^ (-((4 - alpha - α₀) * k))) := by
  refine ⟨Khom α₀ μ, Khom_pos α₀ μ, fun η hη ε hε m n k hmn _ t θ ht hθ => ?_⟩
  calc ∑ D ∈ Pi2 m n, diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ m n D t
      ≤ ∑ _D ∈ Pi2 m n, ENNReal.ofReal (Khom α₀ μ ^ k * Real.exp (2 * θ * t) *
          θ ^ (-((4 - alpha - α₀) * k))) :=
        Finset.sum_le_sum fun D hD =>
          diagram_le_homog (smoothDensity_three hη) hH hε (hPE _) hmn hD ht hθ
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring

/-- **`E:theta-envelope` in `d = 3`** for the Green-smoothed kernels (Step 1 of
`L:crude-corrected`, TeX lines 1993-2009 at revision edf7085f (book 1.1.3)), uniformly in
`η > 0` and `ε > 0`, with the frozen `PairingEnvelopeTarget` as a hypothesis (`θ₀ = 1`). -/
theorem theta_envelope_diagrams_three {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha α₀ Γ μ) (hPE : ∀ N : ℕ, PairingEnvelopeTarget 3 (Fin N)) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t θ : ℝ),
      0 < t → θ₀ ≤ θ →
      ∑ D ∈ Pi2 n n, diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal ((Pi2 n n).card * Real.exp (2 * θ * t) * C ^ n * θ ^ (-(2 * (n : ℝ)))) := by
  obtain ⟨K, hK, hdiag⟩ := homogeneous_envelope_diagrams_three hH hPE
  have hβ : 2 < 4 - alpha - α₀ := by linarith [hH.threshold]
  refine ⟨K, 1, hK, one_pos, fun η hη ε hε n t θ ht hθ => ?_⟩
  have hθ0 : 0 < θ := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [DiagramModel.Pi2_zero_zero, Finset.sum_singleton, DiagramModel.diagram_zero_zero]
    simp only [Finset.card_singleton, Nat.cast_one, one_mul, pow_zero, mul_one,
      CharP.cast_eq_zero, mul_zero, neg_zero, Real.rpow_zero]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
  · refine (hdiag η hη ε hε n n n (by ring) hn t θ ht hθ0).trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : θ ^ (-((4 - alpha - α₀) * n)) ≤ θ ^ (-(2 * (n : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le hθ ?_
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have : 0 ≤ (Pi2 n n).card * K ^ n * Real.exp (2 * θ * t) := by positivity
    calc (Pi2 n n).card * K ^ n * Real.exp (2 * θ * t) * θ ^ (-((4 - alpha - α₀) * n))
        ≤ (Pi2 n n).card * K ^ n * Real.exp (2 * θ * t) * θ ^ (-(2 * (n : ℝ))) := by gcongr
      _ = _ := by ring

/-- **`E:crude-corrected`, diagram half, in `d = 3`** for the Green-smoothed kernels (Step 2 of
`L:crude-corrected`, TeX lines 2036-2041 at revision edf7085f (book 1.1.3)), uniformly in
`η > 0` and `ε > 0`: `Σ_{D ∈ Π_n} J^{(η)}_{n,n,D}(t) ≤ e^{2θ₀t} C^n t^{2n} / n!` for `n ≥ 1`. -/
theorem crude_corrected_diagrams_three {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha α₀ Γ μ) (hPE : ∀ N : ℕ, PairingEnvelopeTarget 3 (Fin N)) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t : ℝ),
      1 ≤ n → 0 < t →
      ∑ D ∈ Pi2 n n, diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ)) := by
  obtain ⟨C₁, θ₀, hC₁, hθ₀, hth⟩ := theta_envelope_diagrams_three hH hPE
  refine ⟨2 * Real.exp 2 * C₁, θ₀, by positivity, hθ₀, fun η hη ε hε n t hn ht => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnt : 0 < (n : ℝ) / t := by positivity
  set θ := θ₀ + n / t with hθdef
  refine (hth η hη ε hε n t θ ht (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp : Real.exp (2 * θ * t) = Real.exp (2 * θ₀ * t) * Real.exp 2 ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, hθdef]
    congr 1
    field_simp
  have hθpow : θ ^ (-(2 * (n : ℝ))) ≤ t ^ (2 * n) / (n : ℝ) ^ (2 * n) := by
    calc θ ^ (-(2 * (n : ℝ))) ≤ ((n : ℝ) / t) ^ (-(2 * (n : ℝ))) :=
          Real.rpow_le_rpow_of_nonpos hnt (by linarith) (by linarith)
      _ = t ^ (2 * n) / (n : ℝ) ^ (2 * n) := by
          rw [Real.rpow_neg hnt.le, show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast, div_pow, inv_div]
  have hcard := CrudeCorrected.card_Pi2_le n
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hnn : (0 : ℝ) < (n : ℝ) ^ (2 * n) := by positivity
  rw [hexp]
  calc (Pi2 n n).card * (Real.exp (2 * θ₀ * t) * Real.exp 2 ^ n) * C₁ ^ n *
        θ ^ (-(2 * (n : ℝ)))
      ≤ (2 ^ n * (n : ℝ) ^ (2 * n) / n !) * (Real.exp (2 * θ₀ * t) * Real.exp 2 ^ n) * C₁ ^ n *
          (t ^ (2 * n) / (n : ℝ) ^ (2 * n)) := by gcongr
    _ = Real.exp (2 * θ₀ * t) * (2 * Real.exp 2 * C₁) ^ n * t ^ (2 * n) / (n ! : ℝ) := by
        field_simp
        ring

/-- **The `d = 3` bridge for the smoothed kernels** (`m4_bridge_of_ne_top` applied to
`green3s`): `J^{(η)}_{m,n,D}(t) ≤ e^{2θt} I_D(e^{-θ·} g_η)` for `θ ≥ 0`, `η > 0`. -/
theorem diagram_le_pairingIntegral_three {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η)
    {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {t θ : ℝ} (ht : 0 < t)
    (hθ : 0 ≤ θ) :
    diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ m n D t ≤
      ENNReal.ofReal (Real.exp (2 * θ * t)) *
        pairingIntegral α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε)
          (fun _ => damp θ (green3s η)) :=
  diagram_le_pairingIntegral hH hε _ _ (measurable_green3s η) (green3s_ne_top hη)
    (smoothedGreen_three_eq hη) hD ht hθ

end StratonovichHAMSecondMoment.EnvelopeD3
