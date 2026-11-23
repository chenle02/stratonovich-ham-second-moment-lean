module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-E, part 3: `P:envelope` (The uniform pairing estimate), main TeX lines
2352-2433 at revision edf7085f (book 1.1.3), deterministic half on the diagram model M4, with
the frozen `PairingInterface.PairingEnvelopeTarget` (`L:pairing-product-envelope`) taken as a
hypothesis (`hPE`), in `d = 1, 2`.

Formalized:
* `two_card_Q1_add_card_Q2`, `prodP_const_le`: `q_0 = q_1`, `q_0 + q_2/2 = |D|` (TeX
  2003-2006, 2395);
* `norms_le_homog` (`E:homogeneous-norms` for the products, `K ≥ max{2N₁(1), N₂(1)², 1}`,
  `Khom`); `diagram_le_homog` and `homogeneous_envelope_diagrams`
  (`E:homogeneous-envelope` for the model diagrams at every noise width `ε > 0`);
* `BK` (`E:B-envelope`, exactly the TeX display with `P_k = (2k-1)!!`, via `termBK`),
  `iInf_exp_rpow` (the infimum `e^{βk}(2t/(βk))^{βk}`, TeX 2412-2413),
  `doubleFactorial_bounds` (`k! ≤ P_k ≤ 2^k k!`), `termBK_le`, `termBK_ge`,
  `summable_termBK_and_le` and `envelope_growth` (`E:envelope-growth`, whole: a statement
  about the numerical majorant only);
* `envelope_paper`: the moment sentences for random variables with the supplied input
  `DiagramModel.MixedMoment` (`P:mixed`), through `moment_le_of_diagrams` (the diagram limits
  `ε ↓ 0`).

Narrower than the TeX (split modelled-object rule): the solution and its chaos are not
constructed (`MixedMoment` supplied); `L:pairing-product-envelope` is the hypothesis `hPE`
(discharged at integration); this module covers `d = 1, 2`: `d = 3` is formalized at the diagram
level for the Green-smoothed kernel uniformly in `η > 0` (modules `GreenSmoothed3`,
`PairingSmoothedNorms`, `EnvelopeD3`, `EnvelopeD3Final`), while the limit `η → 0` and the `d = 3`
moment (`_paper`) versions are not formalized (decision 5 of wave L17).  The TeX's
`η ↓ 0` and `(ε,δ) → 0` limits are the `MixedMoment` limits at a common width `ε`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingDampedNorms
public import StratonovichHAMSecondMoment.D1Upper
public import StratonovichHAMSecondMoment.SeriesType

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.HomogeneousEnvelope

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim MixedMoment coeffALim)
open PairingInterface
open PairingBridge
open PairingDampedNorms

variable {d : ℕ}

/-! ### Counting an admissible product -/

/-- Auxiliary: in an admissible assignment, `2|Q_1| + |Q_2| = 2|D|` (each edge is used once on
`Q_1` or twice on `Q_2`, TeX 1477-1480). -/
theorem two_card_Q1_add_card_Q2 {α : Type*} [DecidableEq α] {L : Finset α}
    {D : Finset (Sym2 α)} (A : Adm L D) : 2 * A.Q1.card + A.Q2.card = 2 * D.card := by
  have hQ1 := Finset.card_eq_sum_card_fiberwise (s := A.Q1) (t := D) (f := A.iota)
    (fun l hl => A.mapsTo l (Finset.mem_union_left _ hl))
  have hQ2 := Finset.card_eq_sum_card_fiberwise (s := A.Q2) (t := D) (f := A.iota)
    (fun l hl => A.mapsTo l (Finset.mem_union_right _ hl))
  rw [hQ1, hQ2, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rcases A.edge e he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2] <;> norm_num

/-- **An admissible product with one kernel and one edge datum** (TeX 2003-2006 and 2392-2396):
`q_0 = q_1` and `q_0 + q_2/2 = |D|` (TeX 1998-2002), so if `N_0 · 2N_1 ≤ Z` and `N_2² ≤ Z` the product is at
most `Z^{|D|}`. -/
theorem prodP_const_le {α : Type*} [DecidableEq α] (a : ℝ) {L : Finset α}
    {D : Finset (Sym2 α)} (E : EdgeData d) (G : Kernel d) (A : Adm L D) {Z : ℝ≥0∞}
    (h1 : N0 G * (2 * N1 a E G) ≤ Z) (h2 : N2 a E G ^ 2 ≤ Z) :
    prodP a (fun _ => E) (fun _ => G) A ≤ Z ^ D.card := by
  have hc := two_card_Q1_add_card_Q2 A
  have hq : A.Q2.card = 2 * (D.card - A.Q1.card) := by omega
  have hle : A.Q1.card ≤ D.card := by omega
  unfold prodP
  simp only [Finset.prod_const]
  rw [A.card01, hq, pow_mul, ← mul_pow]
  calc (N0 G * (2 * N1 a E G)) ^ A.Q1.card * (N2 a E G ^ 2) ^ (D.card - A.Q1.card)
      ≤ Z ^ A.Q1.card * Z ^ (D.card - A.Q1.card) := by gcongr
    _ = Z ^ D.card := by rw [← pow_add, Nat.add_sub_cancel' hle]

/-! ### The homogeneous envelope at every noise width -/

section Homog

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- The constant `K ≥ max{2N₁(1), N₂(1)², 1}` of the proof of `P:envelope` (TeX 2393-2394). -/
def Khom (α₀ : ℝ) (μ : Measure (Rd d)) : ℝ :=
  max (max (2 * DampedNorms.N1 α₀ 1 μ) (DampedNorms.N2sq α₀ 1 μ)) 1

theorem one_le_Khom (α₀ : ℝ) (μ : Measure (Rd d)) : 1 ≤ Khom α₀ μ := le_max_right _ _

theorem Khom_pos (α₀ : ℝ) (μ : Measure (Rd d)) : 0 < Khom α₀ μ :=
  lt_of_lt_of_le one_pos (one_le_Khom α₀ μ)

variable {g : Kernel d} (hgd : GreenDensity d g) (hH : HomogCovariance d alpha α₀ Γ μ)
  {ε : ℝ} (hε : 0 < ε)
include hgd hH hε

/-- The damped kernels satisfy the envelope's kernel hypotheses with the M4 edge datum. -/
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

/-- **`E:homogeneous-norms` for the products** (TeX 2386-2396): `N_0 · 2N_1 ≤ K θ^{-β}` and
`N_2² ≤ K θ^{-β}` with `β = 4 - α - α₀`, for every `θ > 0`. -/
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

/-- **`E:homogeneous-envelope` for one M4 diagram at noise width `ε`** (Step 1 of
`P:envelope`, TeX 2382-2404), with the frozen `PairingEnvelopeTarget` as a hypothesis:
`J_{m,n,D}(t) ≤ K^k e^{2θt} θ^{-βk}` for `m + n = 2k`, every `θ > 0`. -/
theorem diagram_le_homog {m n k : ℕ} (hPE : PairingEnvelopeTarget d (Fin (m + n)))
    (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {t θ : ℝ}
    (ht : 0 < t) (hθ : 0 < θ) :
    diagram (waveGreen d) (covEps Γ ε) α₀ m n D t ≤
      ENNReal.ofReal (Khom α₀ μ ^ k * Real.exp (2 * θ * t) *
        θ ^ (-((4 - alpha - α₀) * k))) := by
  obtain ⟨h1, h2⟩ := norms_le_homog hgd hH hε hθ
  have hβ : 0 < θ ^ (-(4 - alpha - α₀)) := Real.rpow_pos_of_pos hθ _
  have henv : env α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε) (fun _ => damp θ g) ≤
      ENNReal.ofReal (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ^ k := by
    refine iSup_le fun A => ?_
    have := prodP_const_le α₀ (smoothEdge hH hε) (damp θ g) A h1 h2
    rwa [card_D_m4Chain hD hmn] at this
  calc diagram (waveGreen d) (covEps Γ ε) α₀ m n D t
      ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) *
          pairingIntegral α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε) (fun _ => damp θ g) :=
        diagram_le_pairingIntegral hH hε (waveGreen d) g hgd.meas hgd.fin hgd.eq hD ht hθ.le
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

/-- **`E:homogeneous-envelope` for the model diagrams at every noise width** (`P:envelope`,
statement and Step 1, TeX lines 2352-2373 and 2382-2404 at revision edf7085f (book 1.1.3)),
`d = 1, 2`, with the frozen `PairingEnvelopeTarget` (`L:pairing-product-envelope`) as a
hypothesis: there is `K > 0` such
that `Σ_{D ∈ Π} J_{m,n,D}(t) ≤ P_k K^k e^{2θt} θ^{-βk}` for `m + n = 2k ≥ 2`, `θ > 0`, every
`t > 0` and every noise width `ε > 0` (`β = 4 - α - α₀`; `P_k = #Π`). -/
theorem homogeneous_envelope_diagrams {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2)
    (hPE : ∀ N : ℕ, PairingEnvelopeTarget d (Fin N)) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k →
      ∀ t θ : ℝ, 0 < t → 0 < θ →
        ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t ≤
          ENNReal.ofReal ((Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
            θ ^ (-((4 - alpha - α₀) * k))) := by
  obtain ⟨g, hgd⟩ : ∃ g : Kernel d, GreenDensity d g := by
    rcases hd with rfl | rfl
    exacts [⟨_, greenDensity_one⟩, ⟨_, greenDensity_two⟩]
  refine ⟨Khom α₀ μ, Khom_pos α₀ μ, fun ε hε m n k hmn _ t θ ht hθ => ?_⟩
  calc ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t
      ≤ ∑ _D ∈ Pi2 m n, ENNReal.ofReal (Khom α₀ μ ^ k * Real.exp (2 * θ * t) *
          θ ^ (-((4 - alpha - α₀) * k))) :=
        Finset.sum_le_sum fun D hD => diagram_le_homog hgd hH hε (hPE _) hmn hD ht hθ
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring

/-! ### The numerical majorant `B_K` and its growth -/

/-- The `k`-th term of `E:B-envelope`: `(2k+1) P_k K^k inf_{θ>0} e^{2θt} θ^{-βk}` for `k ≥ 1`
(`P_k = (2k-1)!!`), `0` at `k = 0`. -/
def termBK (K β t : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else
    (2 * k + 1) * ((2 * k - 1)‼ : ℝ) * K ^ k *
      ⨅ θ : Ioi (0 : ℝ), Real.exp (2 * θ * t) * (θ : ℝ) ^ (-(β * k))

/-- **`E:B-envelope`** (TeX 2361-2364): `B_K(t) = 1 + Σ_{k ≥ 1} (2k+1) P_k K^k
inf_{θ > 0} e^{2θt} θ^{-βk}`, `P_k = (2k-1)!!`.  (The series converges for `t > 0`, `K > 0`,
`β > 2`: `summable_termBK`.) -/
def BK (K β t : ℝ) : ℝ := 1 + ∑' k : ℕ, termBK K β t k

/-- **The infimum in `E:B-envelope`** (TeX 2412-2413): for `t, c > 0`,
`inf_{θ>0} e^{2θt} θ^{-c} = e^c (2t/c)^c`, attained at `θ = c/(2t)`. -/
theorem iInf_exp_rpow {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    ⨅ θ : Ioi (0 : ℝ), Real.exp (2 * θ * t) * (θ : ℝ) ^ (-c) = Real.exp c * (2 * t / c) ^ c := by
  set θs := c / (2 * t) with hθs
  have hθs0 : 0 < θs := by positivity
  have hpow : θs ^ (-c) = (2 * t / c) ^ c := by
    rw [Real.rpow_neg hθs0.le, ← Real.inv_rpow hθs0.le, hθs, inv_div]
  have hval : Real.exp (2 * θs * t) * θs ^ (-c) = Real.exp c * (2 * t / c) ^ c := by
    rw [hpow, show 2 * θs * t = c by rw [hθs]; field_simp]
  have hlow : ∀ θ : ℝ, 0 < θ → Real.exp c * (2 * t / c) ^ c ≤ Real.exp (2 * θ * t) * θ ^ (-c) := by
    intro θ hθ
    set u := θ / θs with hu
    have hu0 : 0 < u := by positivity
    have hθu : θ = θs * u := by rw [hu]; field_simp
    have h2 : 2 * θ * t = c * u := by rw [hθu, hθs]; field_simp
    rw [h2, hθu, Real.mul_rpow hθs0.le hu0.le, ← hpow]
    have hA : 0 < θs ^ (-c) := Real.rpow_pos_of_pos hθs0 _
    have hB : 0 < u ^ c := Real.rpow_pos_of_pos hu0 _
    have hkey : Real.exp c * u ^ c ≤ Real.exp (c * u) := by
      have h1 : u ^ c ≤ Real.exp (u - 1) ^ c :=
        Real.rpow_le_rpow hu0.le (by linarith [Real.add_one_le_exp (u - 1)]) hc.le
      have h3 : Real.exp (c * u) = Real.exp c * Real.exp (u - 1) ^ c := by
        rw [← Real.exp_mul, ← Real.exp_add]; ring_nf
      rw [h3]
      exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have hneg : u ^ (-c) = (u ^ c)⁻¹ := Real.rpow_neg hu0.le c
    rw [hneg]
    calc Real.exp c * θs ^ (-c) = (Real.exp c * u ^ c) * (u ^ c)⁻¹ * θs ^ (-c) := by
          field_simp
      _ ≤ Real.exp (c * u) * (u ^ c)⁻¹ * θs ^ (-c) := by gcongr
      _ = Real.exp (c * u) * (θs ^ (-c) * (u ^ c)⁻¹) := by ring
  have hbdd : BddBelow (Set.range fun θ : Ioi (0 : ℝ) =>
      Real.exp (2 * θ * t) * (θ : ℝ) ^ (-c)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨θ, rfl⟩
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt θ.2) _)
  refine le_antisymm ?_ (le_ciInf fun θ => hlow θ θ.2)
  exact (ciInf_le hbdd ⟨θs, hθs0⟩).trans_eq hval

/-- Auxiliary: one step of `(2k-1)!!`. -/
theorem doubleFactorial_succ (k : ℕ) : (2 * (k + 1) - 1)‼ = (2 * k + 1) * (2 * k - 1)‼ := by
  rcases k with _ | j
  · rfl
  · rw [show 2 * (j + 1 + 1) - 1 = (2 * j + 1) + 2 by omega, Nat.doubleFactorial_add_two,
      show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    ring

/-- `k! ≤ P_k ≤ 2^k k!` for `P_k = (2k-1)!!` (TeX 2416). -/
theorem doubleFactorial_bounds : ∀ k : ℕ, k ! ≤ (2 * k - 1)‼ ∧ (2 * k - 1)‼ ≤ 2 ^ k * k !
  | 0 => by simp
  | k + 1 => by
    obtain ⟨h1, h2⟩ := doubleFactorial_bounds k
    rw [doubleFactorial_succ, Nat.factorial_succ, pow_succ]
    constructor
    · exact Nat.mul_le_mul (by omega) h1
    · calc (2 * k + 1) * (2 * k - 1)‼ ≤ (2 * (k + 1)) * (2 ^ k * k !) :=
            Nat.mul_le_mul (by omega) h2
        _ = 2 ^ k * 2 * ((k + 1) * k !) := by ring

/-- Auxiliary: `k^k ≤ e^k k!`. -/
theorem pow_self_le_exp_mul_factorial (k : ℕ) : (k : ℝ) ^ k ≤ Real.exp k * k ! := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have h := SeriesType.factorial_ge_exp k hk
    have h2 : Real.exp (1 - k) * Real.exp k = Real.exp 1 := by rw [← Real.exp_add]; ring_nf
    have h3 : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (k : ℝ) ^ k ≤ (k : ℝ) ^ k * Real.exp 1 := le_mul_of_one_le_right (by positivity) h3
      _ = (k : ℝ) ^ k * Real.exp (1 - k) * Real.exp k := by rw [mul_assoc, h2]
      _ ≤ (k ! : ℝ) * Real.exp k := by gcongr
      _ = _ := mul_comm _ _

/-- Auxiliary: `2k + 1 ≤ 3^k` for `k ≥ 1`. -/
theorem two_mul_add_one_le_three_pow : ∀ k : ℕ, 1 ≤ k → 2 * k + 1 ≤ 3 ^ k
  | 0, h => absurd h (by norm_num)
  | 1, _ => by norm_num
  | k + 2, _ => by
    have := two_mul_add_one_le_three_pow (k + 1) (by omega)
    rw [pow_succ]; omega

section Growth

variable {K β : ℝ}

/-- The closed form of the terms (TeX 2412-2413). -/
theorem termBK_eq (hβ : 0 < β) {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    termBK K β t k = (2 * k + 1) * ((2 * k - 1)‼ : ℝ) * K ^ k *
      (Real.exp (β * k) * (2 * t / (β * k)) ^ (β * k)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk' : k ≠ 0 := by omega
  simp only [termBK, hk', ↓reduceIte]
  rw [iInf_exp_rpow ht (by positivity)]

/-- Auxiliary: `e^{βk}(2t/(βk))^{βk} = (e^β (2t/β)^β)^k / ((k^k)^β)`. -/
theorem inf_term_eq (hβ : 0 < β) {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (β * k) * (2 * t / (β * k)) ^ (β * k) =
      (Real.exp β * (2 * t / β) ^ β) ^ k / ((k : ℝ) ^ k) ^ β := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 ≤ 2 * t / β := by positivity
  rw [show 2 * t / (β * k) = (2 * t / β) / k by field_simp, Real.div_rpow hx hk0.le,
    mul_pow, ← Real.rpow_natCast (Real.exp β), ← Real.exp_mul,
    ← Real.rpow_natCast ((2 * t / β) ^ β), ← Real.rpow_mul hx,
    ← Real.rpow_natCast (k : ℝ) k, ← Real.rpow_mul hk0.le]
  rw [mul_comm (k : ℝ) β]
  ring

/-- **Upper bound of the terms** (TeX 2414-2426): for `K > 0`, `β > 2`, `t > 0`, `k ≥ 1`,
`term_k ≤ (b t^β)^k / (k!)^{β-1}` with `b = 6K e^β (2/β)^β`. -/
theorem termBK_le (hK : 0 < K) (hβ : 2 < β) {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    termBK K β t k ≤
      (6 * K * Real.exp β * (2 / β) ^ β * t ^ β) ^ k / (k ! : ℝ) ^ (β - 1) := by
  have hβ0 : 0 < β := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  obtain ⟨-, hP⟩ := doubleFactorial_bounds k
  have hP' : ((2 * k - 1)‼ : ℝ) ≤ 2 ^ k * k ! := by exact_mod_cast hP
  have h3 : (2 * (k : ℝ) + 1) ≤ 3 ^ k := by
    exact_mod_cast two_mul_add_one_le_three_pow k hk
  have hkk : ((k ! : ℝ)) ^ β ≤ ((k : ℝ) ^ k) ^ β :=
    Real.rpow_le_rpow hf.le (by exact_mod_cast Nat.factorial_le_pow k) hβ0.le
  rw [termBK_eq hβ0 ht hk, inf_term_eq hβ0 ht hk]
  set X := Real.exp β * (2 * t / β) ^ β with hX
  have hX0 : 0 ≤ X := by positivity
  have hdenom : 0 < ((k : ℝ) ^ k) ^ β := by positivity
  calc (2 * k + 1) * ((2 * k - 1)‼ : ℝ) * K ^ k * (X ^ k / ((k : ℝ) ^ k) ^ β)
      ≤ 3 ^ k * (2 ^ k * k !) * K ^ k * (X ^ k / (k ! : ℝ) ^ β) := by
        gcongr
    _ = (3 * (2 * (K * X))) ^ k * ((k ! : ℝ) / (k ! : ℝ) ^ β) := by
        rw [mul_pow, mul_pow, mul_pow]; ring
    _ = (3 * (2 * (K * X))) ^ k / (k ! : ℝ) ^ (β - 1) := by
        rw [Real.rpow_sub hf, Real.rpow_one]; field_simp
    _ = _ := by
        congr 2
        rw [hX, show 2 * t / β = (2 / β) * t by ring, Real.mul_rpow (by positivity) ht.le]
        ring

/-- **Lower bound of the terms** (TeX 2414-2426): `term_k ≥ (a t^β)^k / (k!)^{β-1}` with
`a = K (2/β)^β`. -/
theorem termBK_ge (hK : 0 < K) (hβ : 2 < β) {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    (K * (2 / β) ^ β * t ^ β) ^ k / (k ! : ℝ) ^ (β - 1) ≤ termBK K β t k := by
  have hβ0 : 0 < β := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  obtain ⟨hP, -⟩ := doubleFactorial_bounds k
  have hP' : (k ! : ℝ) ≤ ((2 * k - 1)‼ : ℝ) := by exact_mod_cast hP
  have hkk : ((k : ℝ) ^ k) ^ β ≤ (Real.exp k * k !) ^ β :=
    Real.rpow_le_rpow (by positivity) (pow_self_le_exp_mul_factorial k) hβ0.le
  rw [termBK_eq hβ0 ht hk, inf_term_eq hβ0 ht hk]
  have hY : 0 ≤ K * (2 / β) ^ β * t ^ β := by positivity
  have hsplit : (Real.exp k * k !) ^ β = Real.exp β ^ k * (k ! : ℝ) ^ β := by
    rw [Real.mul_rpow (Real.exp_pos _).le hf.le, ← Real.exp_mul, ← Real.rpow_natCast,
      ← Real.exp_mul]
    ring_nf
  calc (K * (2 / β) ^ β * t ^ β) ^ k / (k ! : ℝ) ^ (β - 1)
      = 1 * (k ! : ℝ) * K ^ k * ((Real.exp β * (2 * t / β) ^ β) ^ k /
          (Real.exp β ^ k * (k ! : ℝ) ^ β)) := by
        rw [Real.rpow_sub hf, Real.rpow_one, show 2 * t / β = (2 / β) * t by ring,
          Real.mul_rpow (by positivity) ht.le]
        field_simp
        ring
    _ ≤ (2 * k + 1) * ((2 * k - 1)‼ : ℝ) * K ^ k *
          ((Real.exp β * (2 * t / β) ^ β) ^ k / ((k : ℝ) ^ k) ^ β) := by
        rw [← hsplit]
        gcongr
        all_goals linarith

/-- Auxiliary: the terms are nonnegative for `t > 0`. -/
theorem termBK_nonneg (hK : 0 < K) (hβ : 2 < β) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    0 ≤ termBK K β t k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [termBK]
  · refine le_trans ?_ (termBK_ge hK hβ ht hk)
    have : 0 ≤ K * (2 / β) ^ β * t ^ β := by
      have : 0 < β := by linarith
      positivity
    positivity

/-- **`B_K` converges** and `B_K(t) ≤ exp((β-1)(b t^β)^{1/(β-1)})` (TeX 2426-2428, upper half).
-/
theorem summable_termBK_and_le (hK : 0 < K) (hβ : 2 < β) {t : ℝ} (ht : 0 < t) :
    Summable (termBK K β t) ∧ BK K β t ≤
      Real.exp ((β - 1) * (6 * K * Real.exp β * (2 / β) ^ β * t ^ β) ^ (1 / (β - 1))) := by
  have hβ0 : 0 < β := by linarith
  set x := 6 * K * Real.exp β * (2 / β) ^ β * t ^ β with hx
  have hx0 : 0 ≤ x := by positivity
  obtain ⟨hs, hle⟩ := SeriesType.seriesNu_summable_le (ν := β - 1) (x := x) (by linarith) hx0
  have hdom : ∀ k, termBK K β t k ≤ x ^ k / (k ! : ℝ) ^ (β - 1) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [termBK]
    · exact termBK_le hK hβ ht hk
  have hsum : Summable (termBK K β t) :=
    Summable.of_nonneg_of_le (termBK_nonneg hK hβ ht) hdom hs
  refine ⟨hsum, ?_⟩
  refine le_trans ?_ hle
  rw [BK, hsum.tsum_eq_zero_add, hs.tsum_eq_zero_add]
  have hf0 : termBK K β t 0 = 0 := by simp [termBK]
  have hg0 : x ^ 0 / ((0 ! : ℕ) : ℝ) ^ (β - 1) = 1 := by simp
  rw [hf0, hg0, zero_add]
  have := Summable.tsum_le_tsum (fun k => hdom (k + 1))
    (hsum.comp_injective (add_left_injective 1)) (hs.comp_injective (add_left_injective 1))
  linarith

/-- **`E:envelope-growth`** (TeX 2366-2370; proof, Step 2, 2410-2432): for `K > 0` and
`β > 2` there are `c, C > 0` and `T` with `c t^ρ ≤ log B_K(t) ≤ C t^ρ` for `t ≥ T`,
`ρ = β/(β-1)`.  This concerns the numerical
majorant `B_K` only. -/
theorem envelope_growth (hK : 0 < K) (hβ : 2 < β) :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, T ≤ t →
      c * t ^ (β / (β - 1)) ≤ Real.log (BK K β t) ∧
        Real.log (BK K β t) ≤ C * t ^ (β / (β - 1)) := by
  have hβ0 : 0 < β := by linarith
  have hq : 1 < β - 1 := by linarith
  have hq0 : 0 < β - 1 := by linarith
  set q := β - 1 with hqdef
  set b := 6 * K * Real.exp β * (2 / β) ^ β with hb
  set a := K * (2 / β) ^ β with ha
  have hb0 : 0 < b := by positivity
  have ha0 : 0 < a := by positivity
  set A := a ^ (1 / q) with hA
  have hA0 : 0 < A := by positivity
  set ρ := β / q with hρ
  have hρ0 : 0 < ρ := by positivity
  refine ⟨q * Real.log 2 * A / 4, q * b ^ (1 / q), max 1 ((4 / A) ^ (1 / ρ)), by positivity,
    by positivity, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  obtain ⟨hsum, hup⟩ := summable_termBK_and_le hK hβ ht0
  have hBK1 : 1 ≤ BK K β t := by
    rw [BK]
    have h0 : 0 ≤ ∑' k, termBK K β t k := tsum_nonneg (termBK_nonneg hK hβ ht0)
    linarith
  have hBK0 : 0 < BK K β t := by linarith
  -- the scaling `(c t^β)^{1/q} = c^{1/q} t^ρ`
  have hscale : ∀ c : ℝ, 0 ≤ c → (c * t ^ β) ^ (1 / q) = c ^ (1 / q) * t ^ ρ := by
    intro c hc
    rw [Real.mul_rpow hc (Real.rpow_nonneg ht0.le _), ← Real.rpow_mul ht0.le, hρ]
    congr 2
    field_simp
  constructor
  · -- the lower bound: one term with `k = ⌊A t^ρ / 2⌋`
    have htρ : 4 / A ≤ t ^ ρ := by
      have h := le_trans (le_max_right _ _) ht
      have h4 : 0 ≤ 4 / A := by positivity
      calc 4 / A = ((4 / A) ^ (1 / ρ)) ^ ρ := by
            rw [← Real.rpow_mul h4, one_div_mul_cancel hρ0.ne', Real.rpow_one]
        _ ≤ t ^ ρ := Real.rpow_le_rpow (by positivity) h hρ0.le
    set y := A * t ^ ρ with hy
    have hy4 : 4 ≤ y := by
      rw [hy]; calc (4 : ℝ) = A * (4 / A) := by field_simp
        _ ≤ A * t ^ ρ := by gcongr
    set k := ⌊y / 2⌋₊ with hk
    have hk1 : 1 ≤ k := by
      rw [hk, Nat.one_le_floor_iff]; linarith
    have hkle : (k : ℝ) ≤ y / 2 := Nat.floor_le (by linarith)
    have hkge : y / 4 ≤ (k : ℝ) := by
      have := Nat.lt_floor_add_one (y / 2)
      rw [← hk] at this
      linarith
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    -- the single term is at least `2^{qk}`
    have hterm := termBK_ge hK hβ ht0 hk1
    have hz : (a * t ^ β) ^ (1 / q) = y := by rw [hscale a ha0.le, hy]
    have hfact : (k ! : ℝ) ^ q ≤ ((k : ℝ) ^ k) ^ q :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le_pow k) hq0.le
    have hzt : 0 ≤ a * t ^ β := by positivity
    have h2 : (2 : ℝ) ^ (q * k) ≤ (a * t ^ β) ^ k / (k ! : ℝ) ^ q := by
      have hpow : (a * t ^ β) ^ k = (y ^ q) ^ k := by
        rw [← hz, ← Real.rpow_mul hzt, one_div_mul_cancel hq0.ne', Real.rpow_one]
      rw [hpow]
      calc (2 : ℝ) ^ (q * k) = ((2 * k) ^ q) ^ k / ((k : ℝ) ^ k) ^ q := by
            rw [Real.mul_rpow (by norm_num) hk0.le, mul_pow, ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((k : ℝ) ^ q),
              ← Real.rpow_mul hk0.le, ← Real.rpow_natCast (k : ℝ) k, ← Real.rpow_mul hk0.le]
            rw [mul_comm (k : ℝ) q]
            field_simp
        _ ≤ (y ^ q) ^ k / ((k : ℝ) ^ k) ^ q := by
            gcongr
            linarith
        _ ≤ (y ^ q) ^ k / (k ! : ℝ) ^ q := by
            gcongr
    have hle1 : termBK K β t k ≤ ∑' j, termBK K β t j := by
      simpa using Summable.sum_le_tsum {k} (fun j _ => termBK_nonneg hK hβ ht0 j) hsum
    have hBKge : (2 : ℝ) ^ (q * k) ≤ BK K β t := by
      rw [BK]; linarith [h2.trans hterm]
    have hlog := Real.log_le_log (by positivity) hBKge
    rw [Real.log_rpow (by norm_num)] at hlog
    calc q * Real.log 2 * A / 4 * t ^ ρ = q * Real.log 2 * (y / 4) := by rw [hy]; ring
      _ ≤ q * Real.log 2 * k := by
          gcongr
      _ = q * k * Real.log 2 := by ring
      _ ≤ _ := hlog
  · -- the upper bound
    rw [Real.log_le_iff_le_exp hBK0]
    refine hup.trans (Real.exp_le_exp.2 (le_of_eq ?_))
    rw [hscale b hb0.le]
    ring

end Growth

/-! ### The moment sentences through `MixedMoment` -/

section Moments

variable {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}

/-- Auxiliary: a bound on the model diagram sums, uniform in the noise width, passes to the mixed
moment through `MixedMoment` (the diagram limits `ε ↓ 0`). -/
theorem moment_le_of_diagrams (h : MixedMoment d α₀ Γ P X u t) {m n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ε : ℝ, 0 < ε →
      ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t ≤ ENNReal.ofReal B) :
    ∫ ω, X m ω * X n ω ∂P ≤ B := by
  have hT : Filter.Tendsto
      (fun ε => ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (∑ D ∈ Pi2 m n, diagramLim d Γ α₀ m n D t)) :=
    tendsto_finsetSum _ fun D hD => (h.1 m n D hD).1
  have hle : ∑ D ∈ Pi2 m n, diagramLim d Γ α₀ m n D t ≤ ENNReal.ofReal B :=
    le_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε => hb ε hε)
  rw [(h.2.1 m n).2, ← ENNReal.toReal_sum fun D hD => (h.1 m n D hD).2]
  exact ENNReal.toReal_le_of_le_ofReal hB hle

/-- Auxiliary: a mixed moment bounded for every `θ > 0` by `c e^{2θt} θ^{-βk}` is bounded by
`c inf_θ e^{2θt} θ^{-βk}`. -/
theorem le_mul_iInf {x c β : ℝ} {k : ℕ} (hc : 0 < c)
    (hx : ∀ θ : ℝ, 0 < θ → x ≤ c * (Real.exp (2 * θ * t) * θ ^ (-(β * k)))) :
    x ≤ c * ⨅ θ : Ioi (0 : ℝ), Real.exp (2 * θ * t) * (θ : ℝ) ^ (-(β * k)) := by
  rw [← div_le_iff₀' hc]
  refine le_ciInf fun θ => ?_
  rw [div_le_iff₀' hc]
  exact hx θ θ.2

end Moments

/-- **`P:envelope`, deterministic half with the moment sentences** (TeX lines 2352-2433 at
revision edf7085f (book 1.1.3)), `d = 1, 2`, with the frozen `PairingEnvelopeTarget` as a
hypothesis: there is `K > 0` such that for every `t > 0` and all random variables with
`MixedMoment` (the supplied input `P:mixed`; blocker D5 when this module was written, the
solution and its chaos not constructed; discharged in wave L19 for the chaos terms `srcX` and
their series `srcU` on every source field, `SourceFinal.mixed_terms_l19`),
`E[X_m X_n] ≤ P_k K^k e^{2θt} θ^{-βk}` for `m + n = 2k ≥ 2`, `θ > 0`
(`E:homogeneous-envelope`), and `E u² ≤ B_K(t)` with `β = 4 - α - α₀`. -/
theorem envelope_paper {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2)
    (hPE : ∀ N : ℕ, PairingEnvelopeTarget d (Fin N)) :
    ∃ K : ℝ, 0 < K ∧ (∀ t : ℝ, 0 < t → ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {X : ℕ → Ω → ℝ} {u : Ω → ℝ}, MixedMoment d α₀ Γ P X u t →
        (∀ m n k : ℕ, m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
          ∫ ω, X m ω * X n ω ∂P ≤ (Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
            θ ^ (-((4 - alpha - α₀) * k))) ∧
        ∫ ω, u ω ^ 2 ∂P ≤ BK K (4 - alpha - α₀) t) := by
  obtain ⟨K, hK, hdiag⟩ := homogeneous_envelope_diagrams hH hd hPE
  have hβ : 2 < 4 - alpha - α₀ := by linarith [hH.threshold]
  refine ⟨K, hK, fun t ht Ω _ P X u h => ?_⟩
  have hmix : ∀ m n k : ℕ, m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
      ∫ ω, X m ω * X n ω ∂P ≤ (Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
        θ ^ (-((4 - alpha - α₀) * k)) := fun m n k hmn hk θ hθ =>
    moment_le_of_diagrams h (by positivity) fun ε hε => hdiag ε hε m n k hmn hk t θ ht hθ
  refine ⟨hmix, ?_⟩
  obtain ⟨hsum, -⟩ := summable_termBK_and_le hK hβ ht
  have hA : ∀ k : ℕ, 1 ≤ k → (coeffALim d Γ α₀ k t).toReal ≤ termBK K (4 - alpha - α₀) t k := by
    intro k hk
    have hk' : k ≠ 0 := by omega
    rw [h.coeffA_eq k]
    simp only [termBK, hk', ↓reduceIte]
    have hPk : (0 : ℝ) < ((2 * k - 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
    calc ∑ m ∈ Finset.range (2 * k + 1), ∫ ω, X m ω * X (2 * k - m) ω ∂P
        ≤ ∑ _m ∈ Finset.range (2 * k + 1), ((2 * k - 1)‼ : ℝ) * K ^ k *
            ⨅ θ : Ioi (0 : ℝ), Real.exp (2 * θ * t) * (θ : ℝ) ^ (-((4 - alpha - α₀) * k)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' : m + (2 * k - m) = 2 * k := by
            have := Finset.mem_range.1 hm; omega
          refine le_mul_iInf (by positivity) fun θ hθ => ?_
          have := hmix m (2 * k - m) k hm' hk θ hθ
          rw [DiagramModel.card_Pi2 hm'] at this
          linarith
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hnn : ∀ k, 0 ≤ (coeffALim d Γ α₀ k t).toReal := fun k => ENNReal.toReal_nonneg
  rw [h.secondMoment_eq, h.2.2.2.summable.tsum_eq_zero_add, BK, hsum.tsum_eq_zero_add]
  have h0 : termBK K (4 - alpha - α₀) t 0 = 0 := by simp [termBK]
  rw [h0, zero_add, DiagramModel.coeffALim_zero, ENNReal.toReal_one]
  have := Summable.tsum_le_tsum (fun k => hA (k + 1) (by omega))
    (h.2.2.2.summable.comp_injective (add_left_injective 1))
    (hsum.comp_injective (add_left_injective 1))
  linarith

end StratonovichHAMSecondMoment.HomogeneousEnvelope
