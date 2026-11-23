module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-E, part 4: `L:crude-corrected` (Corrected crude estimate), main TeX lines
1970-2054 at revision edf7085f (book 1.1.3): `E:crude-norms` (1970-1976), `E:theta-envelope`
(Step 1, 1993-2009), the choice `θ = θ₀ + n/t` and the series bound (Step 2, 2036-2053);
deterministic half on the diagram model M4 with the frozen `PairingEnvelopeTarget` as a
hypothesis, in `d = 1, 2`, and the moment sentences through `MixedMoment`.

Formalized: `theta_envelope_diagrams` (`θ₀ = 1`; `E:crude-norms` from `E:homogeneous-norms`
and `β > 2`), `card_Pi2_le` (`P_n n^{-2n} ≤ 2^n/n!`), `crude_corrected_diagrams`
(`C = 2e²K`), `sum_pairs_le_sq`, `sq_sum_sqrt_le` (`(Σ z^n/√n!)² ≤ 2e^{2z²}`),
`moment_le_mul`, `secondMoment_le_crude`, `crude_corrected_paper`.

Route difference: the TeX bounds `‖u‖₂` by Minkowski over the chaos terms; `u` is not
constructed, so the Lean route bounds `E u² = Σ_k Σ_{m ≤ 2k} E[X_m X_{2k-m}]` (`MixedMoment`)
with `E[X_m X_n] ≤ ‖X_m‖ ‖X_n‖` in arithmetic-geometric form, and the same Cauchy-Schwarz bound.
Narrower as in `HomogeneousEnvelope` (`MixedMoment` supplied, `hPE` hypothesis, `d = 1, 2` here:
`d = 3` is formalized at the diagram level for the Green-smoothed kernel uniformly in `η > 0` in
`GreenSmoothed3`, `PairingSmoothedNorms`, `EnvelopeD3` and `EnvelopeD3Final`; the limit `η → 0`
and the `d = 3` moment (`_paper`) versions are not formalized, decision 5 of wave L17).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogeneousEnvelope

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.CrudeCorrected

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim MixedMoment coeffALim)
open PairingInterface
open HomogeneousEnvelope

variable {d : ℕ}

/-- **`E:theta-envelope` for the model diagrams at every noise width** (Step 1 of
`L:crude-corrected`, TeX lines 1993-2009 at revision edf7085f (book 1.1.3)), `d = 1, 2`, with
the frozen `PairingEnvelopeTarget` as a hypothesis: there are `C > 0`, `θ₀ > 0` with
`Σ_{D ∈ Π_n} J_{n,n,D}(t) ≤ P_n e^{2θt} C^n θ^{-2n}` for `θ ≥ θ₀`, every `t > 0`, `n ≥ 0` and
noise width `ε > 0` (`θ₀ = 1`; `E:crude-norms` from `E:homogeneous-norms`, `β > 2`). -/
theorem theta_envelope_diagrams {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2)
    (hPE : ∀ N : ℕ, PairingEnvelopeTarget d (Fin N)) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t θ : ℝ), 0 < t → θ₀ ≤ θ →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal ((Pi2 n n).card * Real.exp (2 * θ * t) * C ^ n * θ ^ (-(2 * (n : ℝ)))) := by
  obtain ⟨K, hK, hdiag⟩ := homogeneous_envelope_diagrams hH hd hPE
  have hβ : 2 < 4 - alpha - α₀ := by linarith [hH.threshold]
  refine ⟨K, 1, hK, one_pos, fun ε hε n t θ ht hθ => ?_⟩
  have hθ0 : 0 < θ := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [DiagramModel.Pi2_zero_zero, Finset.sum_singleton, DiagramModel.diagram_zero_zero]
    simp only [Finset.card_singleton, Nat.cast_one, one_mul, pow_zero, mul_one,
      CharP.cast_eq_zero, mul_zero, neg_zero, Real.rpow_zero]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
  · refine (hdiag ε hε n n n (by ring) hn t θ ht hθ0).trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : θ ^ (-((4 - alpha - α₀) * n)) ≤ θ ^ (-(2 * (n : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le hθ ?_
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have : 0 ≤ (Pi2 n n).card * K ^ n * Real.exp (2 * θ * t) := by positivity
    calc (Pi2 n n).card * K ^ n * Real.exp (2 * θ * t) * θ ^ (-((4 - alpha - α₀) * n))
        ≤ (Pi2 n n).card * K ^ n * Real.exp (2 * θ * t) * θ ^ (-(2 * (n : ℝ))) := by gcongr
      _ = _ := by ring

/-- Auxiliary (TeX 2038-2039): `P_n n^{-2n} ≤ 2^n / n!`, from `(2n)! ≤ (2n)^{2n}`. -/
theorem card_Pi2_le (n : ℕ) : ((Pi2 n n).card : ℝ) ≤ 2 ^ n * (n : ℝ) ^ (2 * n) / n ! := by
  have h := DiagramModel.card_Pi2_mul (m := n) (n := n) (k := n) (by ring)
  have h2 : (2 * n)! ≤ (2 * n) ^ (2 * n) := Nat.factorial_le_pow _
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [le_div_iff₀ hf]
  have : ((Pi2 n n).card : ℝ) * (2 ^ n * n !) ≤ (2 * n : ℝ) ^ (2 * n) := by
    exact_mod_cast h ▸ h2
  have e : (2 * n : ℝ) ^ (2 * n) = 2 ^ n * (n : ℝ) ^ (2 * n) * 2 ^ n := by
    rw [mul_pow, show (2 : ℝ) ^ (2 * n) = 2 ^ n * 2 ^ n by rw [two_mul, pow_add]]; ring
  rw [e] at this
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

/-- **`E:crude-corrected`, diagram half** (Step 2 of `L:crude-corrected`, TeX lines 2036-2041 at
revision edf7085f (book 1.1.3)), `d = 1, 2`, with the frozen `PairingEnvelopeTarget` as a
hypothesis: with `θ = θ₀ + n/t` in `E:theta-envelope`, `P_n n^{-2n} ≤ 2^n/n!` and `2^n e^{2n}`
absorbed in `C^n`, `Σ_{D ∈ Π_n} J_{n,n,D}(t) ≤ e^{2θ₀t} C^n t^{2n} / n!` for `n ≥ 1`, `t > 0`,
every noise width `ε > 0`. -/
theorem crude_corrected_diagrams {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2)
    (hPE : ∀ N : ℕ, PairingEnvelopeTarget d (Fin N)) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t : ℝ), 1 ≤ n → 0 < t →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ)) := by
  obtain ⟨C₁, θ₀, hC₁, hθ₀, hth⟩ := theta_envelope_diagrams hH hd hPE
  refine ⟨2 * Real.exp 2 * C₁, θ₀, by positivity, hθ₀, fun ε hε n t hn ht => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnt : 0 < (n : ℝ) / t := by positivity
  set θ := θ₀ + n / t with hθdef
  refine (hth ε hε n t θ ht (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
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
  have hcard := card_Pi2_le n
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

/-! ### The moment sentences -/

/-- Auxiliary (TeX 2044-2053): the pairs `(m, 2k-m)`, `m ≤ 2k`, `k < K`, are distinct pairs in
`[0, 2K)²`, so `Σ_{k<K} Σ_{m ≤ 2k} b_m b_{2k-m} ≤ (Σ_{n<2K} b_n)²` for `b ≥ 0`. -/
theorem sum_pairs_le_sq (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range (2 * k + 1), b m * b (2 * k - m) ≤
      (∑ n ∈ Finset.range (2 * K), b n) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_sigma']
  set pairMap : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun x => (x.2, 2 * x.1 - x.2) with hpairMap
  have hinj : Set.InjOn pairMap ((Finset.range K).sigma fun k => Finset.range (2 * k + 1)) := by
    rintro ⟨k, m⟩ hx ⟨k', m'⟩ hy hxy
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio] at hx hy
    simp only [hpairMap, Prod.mk.injEq] at hxy
    obtain ⟨rfl, h2⟩ := hxy
    have : k = k' := by omega
    subst this
    rfl
  have himg : ((Finset.range K).sigma fun k => Finset.range (2 * k + 1)).image pairMap ⊆
      Finset.range (2 * K) ×ˢ Finset.range (2 * K) := by
    intro p hp
    obtain ⟨⟨k, m⟩, hx, rfl⟩ := Finset.mem_image.1 hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [hpairMap, Finset.mem_product, Finset.mem_range]
    omega
  calc ∑ x ∈ (Finset.range K).sigma fun k => Finset.range (2 * k + 1), b x.2 * b (2 * x.1 - x.2)
      = ∑ p ∈ ((Finset.range K).sigma fun k => Finset.range (2 * k + 1)).image pairMap,
          b p.1 * b p.2 := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ Finset.range (2 * K) ×ˢ Finset.range (2 * K), b p.1 * b p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ => mul_nonneg (hb _) (hb _)

/-- Auxiliary (TeX 2044-2053, Cauchy-Schwarz): `(Σ_{n<N} √((Ct²)^n/n!))² ≤ 2 e^{2Ct²}`. -/
theorem sq_sum_sqrt_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.range N, Real.sqrt (x ^ n / n !)) ^ 2 ≤ 2 * Real.exp (2 * x) := by
  have hsplit : ∀ n : ℕ, Real.sqrt (x ^ n / n !) =
      Real.sqrt ((1 / 2 : ℝ) ^ n) * Real.sqrt ((2 * x) ^ n / n !) := by
    intro n
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    rw [mul_pow]
    field_simp
    rw [mul_assoc, ← mul_pow]
    norm_num
  simp_rw [hsplit]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  have h1 : ∀ n : ℕ, Real.sqrt ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 2 : ℝ) ^ n :=
    fun n => Real.sq_sqrt (by positivity)
  have h2 : ∀ n : ℕ, Real.sqrt ((2 * x) ^ n / n !) ^ 2 = (2 * x) ^ n / n ! :=
    fun n => Real.sq_sqrt (by positivity)
  simp_rw [h1, h2]
  exact mul_le_mul (sum_geometric_two_le N) (Real.sum_le_exp_of_nonneg (by positivity) N)
    (Finset.sum_nonneg fun n _ => by positivity) (by norm_num)

section Moments

variable {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}

/-- Auxiliary (the arithmetic-geometric mean step): `E[X_m X_n] ≤ b_m b_n` when
`E X_m² ≤ b_m²`, `E X_n² ≤ b_n²`, `b_m, b_n > 0` (the products integrable as in `MixedMoment`).
-/
theorem moment_le_mul (h : MixedMoment d α₀ Γ P X u t) {m n : ℕ} {bm bn : ℝ} (hbm : 0 < bm)
    (hbn : 0 < bn) (hm : ∫ ω, X m ω * X m ω ∂P ≤ bm ^ 2) (hn : ∫ ω, X n ω * X n ω ∂P ≤ bn ^ 2) :
    ∫ ω, X m ω * X n ω ∂P ≤ bm * bn := by
  set r := bn / bm with hr
  have hr0 : 0 < r := by positivity
  have hpt : ∀ ω, X m ω * X n ω ≤ (r * (X m ω * X m ω) + (X n ω * X n ω) / r) / 2 := by
    intro ω
    have := sq_nonneg (r * X m ω - X n ω)
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_nonneg]
    have e : (r * (X m ω * X m ω) + X n ω * X n ω / r) - X m ω * X n ω * 2 =
        (r * X m ω - X n ω) ^ 2 / r := by
      field_simp; ring
    rw [e]; positivity
  have hmm := (h.2.1 m m).1
  have hnn := (h.2.1 n n).1
  have hmn := (h.2.1 m n).1
  calc ∫ ω, X m ω * X n ω ∂P
      ≤ ∫ ω, (r * (X m ω * X m ω) + (X n ω * X n ω) / r) / 2 ∂P :=
        integral_mono hmn (((hmm.const_mul r).add (hnn.div_const r)).div_const 2) hpt
    _ = (r * ∫ ω, X m ω * X m ω ∂P + (∫ ω, X n ω * X n ω ∂P) / r) / 2 := by
        rw [integral_div, integral_add (hmm.const_mul r) (hnn.div_const r), integral_const_mul,
          integral_div]
    _ ≤ (r * bm ^ 2 + bn ^ 2 / r) / 2 := by gcongr
    _ = bm * bn := by rw [hr]; field_simp; ring

/-- **The series step of `L:crude-corrected`** (Step 2, TeX 2041-2053): under `MixedMoment`, if
`E X_n² ≤ e^{2θ₀t} C^n t^{2n}/n!` for every `n ≥ 1` (`θ₀, C, t > 0`), then
`E u² ≤ 2 e^{2θ₀t + 2Ct²}`.  The TeX's Minkowski and Cauchy-Schwarz are taken on the mixed
moments: `E[X_m X_n] ≤ b_m b_n` (`moment_le_mul`), `E u² = Σ_k Σ_{m ≤ 2k} E[X_m X_{2k-m}]`
(`MixedMoment.secondMoment_eq`, `MixedMoment.coeffA_eq`), and the Cauchy-Schwarz bound
`(Σ z^n/√n!)² ≤ 2e^{2z²}`. -/
theorem secondMoment_le_crude (h : MixedMoment d α₀ Γ P X u t) {θ₀ C : ℝ} (hθ₀ : 0 < θ₀)
    (hC : 0 < C) (ht : 0 < t)
    (hX : ∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω * X n ω ∂P ≤
      Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n !) :
    ∫ ω, u ω ^ 2 ∂P ≤ 2 * Real.exp (2 * θ₀ * t + 2 * C * t ^ 2) := by
  set x := C * t ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  set b : ℕ → ℝ := fun n => Real.exp (θ₀ * t) * Real.sqrt (x ^ n / n !) with hb
  have hbpos : ∀ n, 0 < b n := fun n => by
    simp only [hb]
    have : 0 < x ^ n / n ! := by positivity
    positivity
  have hbsq : ∀ n, ∫ ω, X n ω * X n ω ∂P ≤ b n ^ 2 := by
    intro n
    have e : b n ^ 2 = Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n ! := by
      simp only [hb]
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul, hx, mul_pow, ← pow_mul,
        mul_comm 2 n]
      push_cast
      ring_nf
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h.moment_zero_zero, e]
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero]
      exact Real.one_le_exp (by positivity)
    · rw [e]; exact hX n hn
  have hA : ∀ k, (coeffALim d Γ α₀ k t).toReal ≤
      ∑ m ∈ Finset.range (2 * k + 1), b m * b (2 * k - m) := by
    intro k
    rw [h.coeffA_eq k]
    exact Finset.sum_le_sum fun m _ =>
      moment_le_mul h (hbpos m) (hbpos _) (hbsq m) (hbsq _)
  have hB : ∀ K, ∑ k ∈ Finset.range K, (coeffALim d Γ α₀ k t).toReal ≤
      2 * Real.exp (2 * θ₀ * t + 2 * C * t ^ 2) := by
    intro K
    calc ∑ k ∈ Finset.range K, (coeffALim d Γ α₀ k t).toReal
        ≤ ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range (2 * k + 1), b m * b (2 * k - m) :=
          Finset.sum_le_sum fun k _ => hA k
      _ ≤ (∑ n ∈ Finset.range (2 * K), b n) ^ 2 :=
          sum_pairs_le_sq b (fun n => (hbpos n).le) K
      _ = Real.exp (2 * θ₀ * t) * (∑ n ∈ Finset.range (2 * K), Real.sqrt (x ^ n / n !)) ^ 2 := by
          simp only [hb]
          rw [← Finset.mul_sum, mul_pow, ← Real.exp_nat_mul]
          push_cast; ring_nf
      _ ≤ Real.exp (2 * θ₀ * t) * (2 * Real.exp (2 * x)) := by
          gcongr; exact sq_sum_sqrt_le x hx0 _
      _ = _ := by rw [hx, mul_left_comm, ← Real.exp_add]; ring_nf
  rw [h.secondMoment_eq]
  exact Real.tsum_le_of_sum_range_le (fun k => ENNReal.toReal_nonneg) hB

end Moments

/-- **`L:crude-corrected`** (Corrected crude estimate; TeX lines 1978-2054 at revision edf7085f
(book 1.1.3)) in `d = 1, 2`, with the frozen `PairingEnvelopeTarget`
(`L:pairing-product-envelope`) as a hypothesis and the moment sentences for random variables
satisfying the supplied input `MixedMoment` (`P:mixed`; the solution and its chaos are not
constructed): there are `C, θ₀ > 0` such that for every `t > 0`,
`E X_n(t,x)² ≤ e^{2θ₀t} C^n t^{2n}/n!` for `n ≥ 1` and `E u²(t,x) ≤ 2e^{2θ₀t + 2Ct²}`
(`E:crude-corrected`). -/
theorem crude_corrected_paper {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2)
    (hPE : ∀ N : ℕ, PairingEnvelopeTarget d (Fin N)) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ t : ℝ, 0 < t → ∀ {Ω : Type} [MeasurableSpace Ω]
      {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ}, MixedMoment d α₀ Γ P X u t →
      (∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω ^ 2 ∂P ≤ Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n !) ∧
      ∫ ω, u ω ^ 2 ∂P ≤ 2 * Real.exp (2 * θ₀ * t + 2 * C * t ^ 2) := by
  obtain ⟨C, θ₀, hC, hθ₀, hdiag⟩ := crude_corrected_diagrams hH hd hPE
  refine ⟨C, θ₀, hC, hθ₀, fun t ht Ω _ P X u h => ?_⟩
  have hX : ∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω * X n ω ∂P ≤
      Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n ! := fun n hn =>
    moment_le_of_diagrams h (by positivity) fun ε hε => hdiag ε hε n t hn ht
  refine ⟨fun n hn => ?_, secondMoment_le_crude h hθ₀ hC ht hX⟩
  simp_rw [sq]
  exact hX n hn

end StratonovichHAMSecondMoment.CrudeCorrected
