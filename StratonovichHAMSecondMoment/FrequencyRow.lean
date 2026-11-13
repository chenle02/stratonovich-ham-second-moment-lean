module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Proposition `P:frequency-row` (Uniform scalar row, TeX lines 47-139) and
Corollary `C:frequency-time` (A time exponent above one half, TeX lines
141-165) of `notes/integrated_wave_variance.tex` (revision a284420), with the
definitions `E:variance-scale-profile` (l. 12-20), `E:frequency-row-kernel` and
`E:frequency-row-integral` (l. 33-42).

Objects.
* `bracket` and `frequencyPair` (`𝒬_h` of `E:masked-frequency-pair`) are reused
  from `MaskedTrigProducts`.
* `rowKernel a h ξ η = 𝒬_h(|ξ|,|η|)/(⟨ξ⟩⟨η⟩)` is `Φ_h`.
* `rowIntegral a γ h ν ξ = ofReal(⟨ξ⟩^{2γ}) · ∫⁻ ofReal(Φ_h(ξ,ξ-λ)) dν(λ)` is
  `J_h(ξ)`, the nonnegative extended integral of TeX l. 43 (a lower Lebesgue
  integral; no Bochner junk value enters it).
* `scaleProfile α h` is `B_α(h)`.

What is proved (no supplied inputs; class same-assumptions).
* `frequency_row`: under `a < 1`, `α + a < 2`, `2γ ≤ 1`, `α + 2γ < 2`,
  `∃ K ≥ 0, ∀ d ν C, C ≥ 0 → growth → ∀ h ∈ (0,1], sup_ξ J_h(ξ) ≤ K C B_α(h)`,
  and for every `ξ` the kernel `λ ↦ Φ_h(ξ,ξ-λ)` is `ν`-integrable with
  `⟨ξ⟩^{2γ} ∫ Φ_h(ξ,ξ-λ) dν ≤ K C B_α(h)` (the TeX's "finiteness of the original
  integral", l. 136-137). The order `∃ K, ∀ d ν C h ξ` encodes that `K` does not
  depend on `d, ν, C, h, ξ` (TeX l. 48-49).
* `frequency_time`: for `2β < 2 - a`, `2β < 3 - a - α` (and the same hypotheses),
  `∃ K_β ≥ 0, ∀ d ν C h, h^{2-a} sup_ξ J_h(ξ) ≤ K_β C h^{2β}`.
* `frequency_row_paper`, `frequency_time_paper`: the same with the manuscript's
  hypotheses: `H:homog` (`HomogCovariance d α a Γ μ`, with `a = α₀`, TeX l. 5-6),
  `0 < γ < min(1/2, (2-α)/2)` (`E:variance-gamma-range`), a positive Radon
  measure `ν` (`IsLocallyFiniteMeasure ν`), `C ≥ 0`, the growth bound
  `E:frequency-translated-growth`, and for the corollary
  `1/2 < β < min(1 - a/2, (3-a-α)/2)` (`E:variance-beta-range`). The constants
  are chosen before `d, Γ, μ, ν, C, h`.

Implicit hypotheses made explicit / reading choices.
* `B(y,r)` in `E:frequency-translated-growth` is read as the open ball, the weaker
  hypothesis; the closed-ball bound is derived (`closedBall_le`, TeX l. 29-31).
* `ν` is a measure on the Borel σ-algebra of `ℝ^d`. Measurability of the kernel
  in `λ` is proved (it is continuous), not assumed.

Hypotheses carried but unused. In the wrappers: `0 < γ` (only `2γ ≤ 1` and
`α + 2γ < 2` are used), `1/2 < β`, `IsLocallyFiniteMeasure ν`, and all of
`H:homog` except `α₀ < 1` and `α₀ + α < 2`. The general theorems hold for every
`d` (including `d = 0`) and every real `α` satisfying the numerical hypotheses.

Proof route (differs from the TeX in its bookkeeping, not in its mathematics).
The integrand is bounded pointwise by two dyadic shell majorants: around `ξ` on
the near region `|λ| ≤ 4|ξ|` and around `0` on the far region `|λ| > 4|ξ|`
(the TeX splits at `4q`, `q = max(1,|ξ|)`; the split at `4|ξ|` needs no `q`).
Shells are closed balls of radius `2^j`, so their masses are bounded by the
growth hypothesis directly (`le_shellSum`, `lintegral_shellSum`, `shellSum_le`).
Near region: on the shell `2^n ≤ |η| ≤ 2^{n+1}` we use `⟨ξ⟩ ≥ 2^n/5`, so
`⟨ξ⟩^{2γ-1} ≤ (2^n/5)^{2γ-1}`; this gives the geometric ratio `2^{α+2γ-2} < 1`
in all three cases of `α` at once, instead of the TeX's three-case bound on
`A_ξ(q)` (l. 60-99). Far region: as in the TeX (l. 101-120), with the series
`rowSeries`; the bound `S(h) ≤ K_{α,a} B_α(h)` (`rowSeries_tsum_le`) splits at
the first `M` with `h 2^M > 1` (`M = L + 1` of TeX l. 121) and treats the three
cases as in TeX l. 121-135. The corollary follows TeX l. 155-163
(`scale_time_le`). Lemmas marked auxiliary serve only this Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MaskedTrigProducts
public import StratonovichHAMSecondMoment.HomogHypothesis

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Metric Filter Topology
open StratonovichHAMSecondMoment.MaskedTrigProducts (bracket frequencyPair)
open StratonovichHAMSecondMoment.HomogHypothesis (Rd HomogCovariance)

namespace StratonovichHAMSecondMoment.FrequencyRow

/-- `⟨x⟩ ≥ 1` (auxiliary to the Lean proof route). -/
theorem one_le_bracket (x : ℝ) : 1 ≤ bracket x := by
  unfold bracket
  rw [Real.le_sqrt' one_pos]; nlinarith [sq_nonneg x]

/-- `⟨x⟩ > 0` (auxiliary to the Lean proof route). -/
theorem bracket_pos (x : ℝ) : 0 < bracket x := lt_of_lt_of_le one_pos (one_le_bracket x)

/-- `|x| ≤ ⟨x⟩` (auxiliary to the Lean proof route). -/
theorem abs_le_bracket (x : ℝ) : |x| ≤ bracket x := by
  unfold bracket
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])

/-- `⟨·⟩` is monotone in `|x|` (auxiliary to the Lean proof route). -/
theorem bracket_mono {x y : ℝ} (h : |x| ≤ |y|) : bracket x ≤ bracket y := by
  unfold bracket
  apply Real.sqrt_le_sqrt
  have := sq_le_sq.mpr (by simpa [abs_abs] using h : |x| ≤ |y|)
  linarith

/-- `⟨·⟩` is continuous (auxiliary to the Lean proof route). -/
theorem continuous_bracket : Continuous bracket := by
  unfold bracket; fun_prop

/-- For `a < 1` a bracket power `⟨x⟩^{a-1}` is at most one
(auxiliary to the Lean proof route). -/
theorem bracket_rpow_le_one {a : ℝ} (ha : a < 1) (x : ℝ) : bracket x ^ (a - 1) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_bracket x) (by linarith)

/-- `⟨x⟩^e ≥ 0` (auxiliary to the Lean proof route). -/
theorem bracket_rpow_nonneg (e x : ℝ) : 0 ≤ bracket x ^ e :=
  Real.rpow_nonneg (bracket_pos x).le _

/-- If `|x| ≥ t/2` with `t ≥ 0`, then `⟨x⟩^{a-1} ≤ 2^{1-a} ⟨t⟩^{a-1}` for `a < 1`
(the bracket bound of TeX l. 107). -/
theorem bracket_rpow_le_half {a : ℝ} (ha : a < 1) {x t : ℝ} (ht : 0 ≤ t) (hx : t / 2 ≤ |x|) :
    bracket x ^ (a - 1) ≤ (2 : ℝ) ^ (1 - a) * bracket t ^ (a - 1) := by
  have hb : bracket t / 2 ≤ bracket x := by
    unfold bracket
    rw [show Real.sqrt (1 + t ^ 2) / 2 = Real.sqrt ((1 + t ^ 2) / 4) by
      rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have h1 : (t / 2) ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (by positivity) hx 2
    nlinarith
  have h2 : 0 < bracket t / 2 := by have := bracket_pos t; positivity
  calc bracket x ^ (a - 1) ≤ (bracket t / 2) ^ (a - 1) :=
        Real.rpow_le_rpow_of_nonpos h2 hb (by linarith)
    _ = (2 : ℝ) ^ (1 - a) * bracket t ^ (a - 1) := by
        rw [Real.div_rpow (bracket_pos t).le (by norm_num), div_eq_mul_inv, mul_comm,
          ← Real.rpow_neg (by norm_num), neg_sub]

/-- `𝒬_h ≥ 0` (auxiliary to the Lean proof route). -/
theorem frequencyPair_nonneg (a h r ρ : ℝ) : 0 ≤ frequencyPair a h r ρ := by
  unfold frequencyPair
  exact add_nonneg (bracket_rpow_nonneg _ _) (bracket_rpow_nonneg _ _)

/-- `𝒬_h ≤ 2` for `a < 1`: both bracket powers are at most one (a step of the
TeX proof of `P:frequency-row`, l. 86-87). -/
theorem frequencyPair_le_two {a : ℝ} (ha : a < 1) (h r ρ : ℝ) : frequencyPair a h r ρ ≤ 2 := by
  unfold frequencyPair
  linarith [bracket_rpow_le_one ha (h * (r - ρ)), bracket_rpow_le_one ha (h * (r + ρ))]

/-- `((2:ℝ)^n)^α = (2^α)^n`. Auxiliary to the Lean proof route. -/
theorem two_pow_rpow (n : ℕ) (α : ℝ) : ((2 : ℝ) ^ n) ^ α = ((2 : ℝ) ^ α) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

/-! ### Dyadic shells -/

/-- Pointwise shell majorant (auxiliary to the Lean proof route): if `F ≤ c 0` when
`‖x - y‖ ≤ 1` and `F ≤ c (n+1)` when `2^n ≤ ‖x - y‖ ≤ 2^{n+1}`, then
`F ≤ ∑' j, 1_{closedBall y 2^j}(x) c j`. -/
theorem le_shellSum {E : Type*} [SeminormedAddCommGroup E] (y x : E) (F : ENNReal)
    (c : ℕ → ENNReal) (h0 : ‖x - y‖ ≤ 1 → F ≤ c 0)
    (hs : ∀ n : ℕ, (2 : ℝ) ^ n ≤ ‖x - y‖ → ‖x - y‖ ≤ 2 ^ (n + 1) → F ≤ c (n + 1)) :
    F ≤ ∑' j, (closedBall y ((2 : ℝ) ^ j)).indicator (fun _ => c j) x := by
  by_cases h1 : ‖x - y‖ ≤ 1
  · refine le_trans ?_ (ENNReal.le_tsum 0)
    rw [Set.indicator_of_mem (by simpa [mem_closedBall, dist_eq_norm] using h1)]
    exact h0 h1
  · replace h1 := not_le.mp h1
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1.le (by norm_num : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum (n + 1))
    rw [Set.indicator_of_mem (by simpa [mem_closedBall, dist_eq_norm] using hn2.le)]
    exact hs n hn1 hn2.le

/-- Integral of the shell majorant (auxiliary to the Lean proof route); any measure on a
normed group with its Borel σ-algebra. -/
theorem lintegral_shellSum {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (ν : Measure E) (y : E) (c : ℕ → ENNReal) :
    ∫⁻ x, ∑' j, (closedBall y ((2 : ℝ) ^ j)).indicator (fun _ => c j) x ∂ν =
      ∑' j, c j * ν (closedBall y ((2 : ℝ) ^ j)) := by
  rw [lintegral_tsum fun j => (measurable_const.indicator measurableSet_closedBall).aemeasurable]
  congr 1; funext j
  exact lintegral_indicator_const measurableSet_closedBall _

/-- The open-ball growth bound gives the closed-ball bound (TeX l. 29-31: apply it at
radius `r + ε` and let `ε ↓ 0`). Any measure on a pseudometric space. -/
theorem closedBall_le {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] (ν : Measure E)
    {C α : ℝ} (hgrowth : ∀ y : E, ∀ r : ℝ, 0 < r → ν (ball y r) ≤ ENNReal.ofReal (C * r ^ α))
    (y : E) {R : ℝ} (hR : 0 < R) :
    ν (closedBall y R) ≤ ENNReal.ofReal (C * R ^ α) := by
  have hT : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * (R + ε) ^ α)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (C * R ^ α))) := by
    apply ENNReal.tendsto_ofReal
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have : Continuous fun ε : ℝ => R + ε := by fun_prop
    have hc : ContinuousAt (fun ε : ℝ => C * (R + ε) ^ α) 0 := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.rpow_const this.continuousAt
      left; simp [hR.ne']
    simpa using hc.tendsto
  apply ge_of_tendsto hT
  filter_upwards [self_mem_nhdsWithin] with ε hε
  calc ν (closedBall y R) ≤ ν (ball y (R + ε)) :=
        measure_mono (closedBall_subset_ball (by linarith [show (0:ℝ) < ε from hε]))
    _ ≤ _ := hgrowth y _ (by linarith [show (0:ℝ) < ε from hε])

/-- Shell sum bounded by the growth constant (auxiliary to the Lean proof route). -/
theorem shellSum_le {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] (ν : Measure E)
    {C α : ℝ}
    (hgrowth : ∀ y : E, ∀ r : ℝ, 0 < r → ν (ball y r) ≤ ENNReal.ofReal (C * r ^ α))
    (y : E) (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) :
    ∑' j, ENNReal.ofReal (c j) * ν (closedBall y ((2 : ℝ) ^ j)) ≤
      ∑' j, ENNReal.ofReal (c j * C * ((2 : ℝ) ^ α) ^ j) := by
  apply ENNReal.tsum_le_tsum; intro j
  calc ENNReal.ofReal (c j) * ν (closedBall y ((2 : ℝ) ^ j))
      ≤ ENNReal.ofReal (c j) * ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ α) :=
        by gcongr; exact closedBall_le ν hgrowth y (by positivity)
    _ = _ := by rw [← ENNReal.ofReal_mul (hc j), two_pow_rpow, mul_assoc]


/-! ### The scale profile and the far series -/

/-- The scale profile `B_α(h)` of `E:variance-scale-profile` (TeX l. 12-19):
`1` for `α < 1`, `1 + log(1/h)` for `α = 1`, `h^{1-α}` for `α > 1`. -/
def scaleProfile (α h : ℝ) : ℝ :=
  if α < 1 then 1 else if α = 1 then 1 + Real.log (1 / h) else h ^ (1 - α)

/-- `B_α(h) ≥ 1` for `0 < h ≤ 1` (used at TeX l. 134). -/
theorem one_le_scaleProfile (α : ℝ) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    1 ≤ scaleProfile α h := by
  unfold scaleProfile
  split_ifs with hα hα'
  · exact le_rfl
  · have : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
    linarith
  · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by
      rcases lt_or_gt_of_ne hα' with h' | h' <;> [exact absurd h' hα; linarith])

/-- The dyadic series `S(h) = ∑_j 2^{j(α-1)} ⟨h 2^j⟩^{a-1}` of TeX l. 117-120, term `j`. -/
def rowSeries (α a h : ℝ) (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (α - 1)) ^ n * bracket (h * 2 ^ n) ^ (a - 1)

/-- Terms of `S(h)` are nonnegative (auxiliary to the Lean proof route). -/
theorem rowSeries_nonneg (α a h : ℝ) (n : ℕ) : 0 ≤ rowSeries α a h n :=
  mul_nonneg (by positivity) (bracket_rpow_nonneg _ _)

/-- Head majorant of a term (auxiliary to the Lean proof route). -/
theorem rowSeries_le_head {α a : ℝ} (ha : a < 1) (h : ℝ) (n : ℕ) :
    rowSeries α a h n ≤ ((2 : ℝ) ^ (α - 1)) ^ n := by
  unfold rowSeries
  have := bracket_rpow_le_one ha (h * 2 ^ n)
  have : (0 : ℝ) ≤ ((2 : ℝ) ^ (α - 1)) ^ n := by positivity
  nlinarith

/-- Tail majorant of a term (auxiliary to the Lean proof route). -/
theorem rowSeries_le_tail {α a h : ℝ} (ha : a < 1) (h0 : 0 < h) (n : ℕ) :
    rowSeries α a h n ≤ h ^ (a - 1) * ((2 : ℝ) ^ (α + a - 2)) ^ n := by
  unfold rowSeries
  have hx : 0 < h * 2 ^ n := by positivity
  have h1 : bracket (h * 2 ^ n) ^ (a - 1) ≤ (h * 2 ^ n) ^ (a - 1) :=
    Real.rpow_le_rpow_of_nonpos hx
      (by simpa [abs_of_pos hx] using abs_le_bracket (h * 2 ^ n)) (by linarith)
  have h2 : (h * 2 ^ n) ^ (a - 1) = h ^ (a - 1) * ((2 : ℝ) ^ (a - 1)) ^ n := by
    rw [Real.mul_rpow h0.le (by positivity), two_pow_rpow]
  have h3 : ((2 : ℝ) ^ (α + a - 2)) ^ n = ((2 : ℝ) ^ (α - 1)) ^ n * ((2 : ℝ) ^ (a - 1)) ^ n := by
    rw [← mul_pow, ← Real.rpow_add (by norm_num)]; ring_nf
  rw [h3]
  calc ((2 : ℝ) ^ (α - 1)) ^ n * bracket (h * 2 ^ n) ^ (a - 1)
      ≤ ((2 : ℝ) ^ (α - 1)) ^ n * (h * 2 ^ n) ^ (a - 1) := by gcongr
    _ = _ := by rw [h2]; ring

/-- `2^s < 1` for `s < 0` (auxiliary to the Lean proof route). -/
theorem two_rpow_lt_one {s : ℝ} (hs : s < 0) : (2 : ℝ) ^ s < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hs

/-- `S(h)` converges for `h > 0`, `a < 1`, `α + a < 2` (auxiliary to the Lean proof route). -/
theorem summable_rowSeries {α a h : ℝ} (ha : a < 1) (hαa : α + a < 2) (h0 : 0 < h) :
    Summable (rowSeries α a h) :=
  Summable.of_nonneg_of_le (rowSeries_nonneg α a h) (rowSeries_le_tail ha h0)
    ((summable_geometric_of_lt_one (by positivity) (two_rpow_lt_one (by linarith))).mul_left _)

/-- The estimate `S(h) ≤ K_{α,a} B_α(h)` (TeX l. 120-133), with `K` independent of `h`. -/
theorem rowSeries_tsum_le {α a : ℝ} (ha : a < 1) (hαa : α + a < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∑' n, rowSeries α a h n ≤ K * scaleProfile α h := by
  set r : ℝ := (2 : ℝ) ^ (α - 1) with hr
  set ρ : ℝ := (2 : ℝ) ^ (α + a - 2) with hρ
  have hρ1 : ρ < 1 := two_rpow_lt_one (by linarith)
  have hρ0 : 0 < ρ := by positivity
  have hr0 : 0 < r := by positivity
  -- generic split for each `h`
  have key : ∀ h : ℝ, 0 < h → h ≤ 1 → ∃ M : ℕ, 1 ≤ M ∧ h * 2 ^ (M - 1) ≤ 1 ∧
      ∑' n, rowSeries α a h n ≤ ∑ i ∈ Finset.range M, r ^ i + h ^ (1 - α) * (1 - ρ)⁻¹ := by
    intro h h0 h1
    have hex : ∃ n : ℕ, 1 < h * 2 ^ n := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / h) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, by rwa [div_lt_iff₀ h0, mul_comm] at hn⟩
    classical
    set M := Nat.find hex with hM
    have hMspec : 1 < h * 2 ^ M := Nat.find_spec hex
    have hM1 : 1 ≤ M := by
      rcases Nat.eq_zero_or_pos M with h' | h'
      · rw [h'] at hMspec; simp at hMspec; linarith
      · exact h'
    have hMm : h * 2 ^ (M - 1) ≤ 1 := not_lt.mp (Nat.find_min hex (by omega))
    refine ⟨M, hM1, hMm, ?_⟩
    have hs := summable_rowSeries ha hαa h0
    rw [← hs.sum_add_tsum_nat_add M]
    gcongr with i hi
    · exact rowSeries_le_head ha h i
    · have hg : Summable fun i : ℕ => h ^ (a - 1) * ρ ^ (i + M) := by
        simp_rw [pow_add]
        exact ((summable_geometric_of_lt_one hρ0.le hρ1).mul_right _).mul_left _
      calc ∑' i, rowSeries α a h (i + M) ≤ ∑' i : ℕ, h ^ (a - 1) * ρ ^ (i + M) :=
            Summable.tsum_le_tsum (fun i => rowSeries_le_tail ha h0 _)
              ((summable_nat_add_iff M).mpr hs) hg
        _ = h ^ (a - 1) * ρ ^ M * (1 - ρ)⁻¹ := by
            simp_rw [pow_add]
            rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hρ0.le hρ1]; ring
        _ ≤ h ^ (1 - α) * (1 - ρ)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (by linarith))
            · have e : h ^ (a - 1) * ρ ^ M = h ^ (1 - α) * (h * 2 ^ M) ^ (α + a - 2) := by
                rw [Real.mul_rpow h0.le (by positivity), two_pow_rpow, ← hρ, ← mul_assoc,
                  ← Real.rpow_add h0]; ring_nf
              rw [e]
              have : (h * 2 ^ M) ^ (α + a - 2) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos hMspec.le (by linarith)
              have : 0 ≤ h ^ (1 - α) := by positivity
              nlinarith
  rcases lt_trichotomy α 1 with hα | hα | hα
  · -- α < 1
    have hr1 : r < 1 := two_rpow_lt_one (by linarith)
    refine ⟨(1 - r)⁻¹ + (1 - ρ)⁻¹, by
      have := inv_nonneg.mpr (show (0:ℝ) ≤ 1 - r by linarith)
      have := inv_nonneg.mpr (show (0:ℝ) ≤ 1 - ρ by linarith); linarith, ?_⟩
    intro h h0 h1
    obtain ⟨M, -, -, hS⟩ := key h h0 h1
    have hB : scaleProfile α h = 1 := by simp [scaleProfile, hα]
    rw [hB, mul_one]
    have e1 : ∑ i ∈ Finset.range M, r ^ i ≤ (1 - r)⁻¹ := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := M) hr0.le hr1
      rwa [pow_zero, one_div, ← Finset.range_eq_Ico] at this
    have e2 : h ^ (1 - α) ≤ 1 := Real.rpow_le_one h0.le h1 (by linarith)
    have e3 : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.mpr (by linarith)
    nlinarith
  · -- α = 1
    subst hα
    refine ⟨2 + (1 - ρ)⁻¹, by have := inv_nonneg.mpr (show (0:ℝ) ≤ 1 - ρ by linarith); linarith, ?_⟩
    intro h h0 h1
    obtain ⟨M, hM1, hMm, hS⟩ := key h h0 h1
    have hB : scaleProfile 1 h = 1 + Real.log (1 / h) := by simp [scaleProfile]
    rw [hB]
    have hr1 : r = 1 := by simp [hr]
    have e1 : ∑ i ∈ Finset.range M, r ^ i = M := by simp [hr1]
    have hL : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
    have e2 : ((M : ℝ) - 1) * Real.log 2 ≤ Real.log (1 / h) := by
      have : (2 : ℝ) ^ (M - 1) ≤ 1 / h := by rw [le_div_iff₀ h0]; linarith
      have := Real.log_le_log (by positivity) this
      rw [Real.log_pow, Nat.cast_sub hM1] at this; simpa using this
    have e3 : (M : ℝ) - 1 ≤ 2 * Real.log (1 / h) := by
      by_contra hc; push Not at hc
      have : 0 < (M : ℝ) - 1 := by linarith
      nlinarith
    have e4 : h ^ (1 - (1 : ℝ)) = 1 := by simp
    rw [e1, e4] at hS
    have e5 : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.mpr (by linarith)
    nlinarith
  · -- α > 1
    have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
    refine ⟨r / (r - 1) + (1 - ρ)⁻¹, by
      have : 0 ≤ r / (r - 1) := div_nonneg hr0.le (by linarith)
      have := inv_nonneg.mpr (show (0:ℝ) ≤ 1 - ρ by linarith); linarith, ?_⟩
    intro h h0 h1
    obtain ⟨M, hM1, hMm, hS⟩ := key h h0 h1
    have hB : scaleProfile α h = h ^ (1 - α) := by
      simp [scaleProfile, not_lt.mpr hα.le, hα.ne']
    rw [hB]
    have e1 : ∑ i ∈ Finset.range M, r ^ i ≤ r ^ M / (r - 1) := by
      rw [geom_sum_eq hr1.ne' M, div_le_div_iff_of_pos_right (by linarith)]; linarith
    have e2 : r ^ M ≤ r * h ^ (1 - α) := by
      have hpow : r ^ M = r * ((2 : ℝ) ^ (M - 1)) ^ (α - 1) := by
        rw [two_pow_rpow, ← pow_succ']; congr 1; omega
      rw [hpow]
      gcongr
      calc ((2 : ℝ) ^ (M - 1)) ^ (α - 1) ≤ (1 / h) ^ (α - 1) :=
            Real.rpow_le_rpow (by positivity) (by rw [le_div_iff₀ h0]; linarith) (by linarith)
        _ = h ^ (1 - α) := by
            rw [one_div, Real.inv_rpow h0.le, ← Real.rpow_neg h0.le, neg_sub]
    have e3 : ∑ i ∈ Finset.range M, r ^ i ≤ r / (r - 1) * h ^ (1 - α) := by
      calc _ ≤ r ^ M / (r - 1) := e1
        _ ≤ r * h ^ (1 - α) / (r - 1) := by gcongr
        _ = _ := by ring
    nlinarith


/-! ### The kernel, the row integral and pointwise bounds -/

/-- The kernel `Φ_h(ξ,η) = 𝒬_h(|ξ|,|η|)/(⟨ξ⟩⟨η⟩)` of `E:frequency-row-kernel` (TeX l. 33-37),
with `𝒬_h = frequencyPair` of `E:masked-frequency-pair`. -/
def rowKernel {d : ℕ} (a h : ℝ) (ξ η : Rd d) : ℝ :=
  frequencyPair a h ‖ξ‖ ‖η‖ / (bracket ‖ξ‖ * bracket ‖η‖)

/-- The row integral `J_h(ξ) = ⟨ξ⟩^{2γ} ∫ Φ_h(ξ, ξ-λ) ν(dλ)` of `E:frequency-row-integral`
(TeX l. 38-41), as a nonnegative extended integral (TeX l. 42). -/
def rowIntegral {d : ℕ} (a γ h : ℝ) (ν : Measure (Rd d)) (ξ : Rd d) : ENNReal :=
  ENNReal.ofReal (bracket ‖ξ‖ ^ (2 * γ)) * ∫⁻ l, ENNReal.ofReal (rowKernel a h ξ (ξ - l)) ∂ν

/-- `Φ_h ≥ 0`. -/
theorem rowKernel_nonneg {d : ℕ} (a h : ℝ) (ξ η : Rd d) : 0 ≤ rowKernel a h ξ η :=
  div_nonneg (frequencyPair_nonneg _ _ _ _)
    (mul_nonneg (bracket_pos _).le (bracket_pos _).le)

/-- `λ ↦ Φ_h(ξ, ξ-λ)` is continuous, hence Borel measurable (auxiliary to the Lean proof route). -/
theorem continuous_rowKernel {d : ℕ} (a h : ℝ) (ξ : Rd d) :
    Continuous fun l : Rd d => rowKernel a h ξ (ξ - l) := by
  unfold rowKernel frequencyPair
  have hb : ∀ f : Rd d → ℝ, Continuous f → ∀ e : ℝ, Continuous fun l => bracket (f l) ^ e :=
    fun f hf e => (continuous_bracket.comp hf).rpow_const fun l => Or.inl (bracket_pos _).ne'
  refine Continuous.div ?_ ?_ fun l => (mul_pos (bracket_pos _) (bracket_pos _)).ne'
  · exact (hb _ (by fun_prop) _).add (hb _ (by fun_prop) _)
  · exact continuous_const.mul (continuous_bracket.comp (by fun_prop))

/-- The weighted kernel equals `⟨ξ⟩^{2γ-1} 𝒬_h / ⟨η⟩` (auxiliary to the Lean proof route). -/
theorem weighted_eq {d : ℕ} (a γ h : ℝ) (ξ η : Rd d) :
    bracket ‖ξ‖ ^ (2 * γ) * rowKernel a h ξ η =
      bracket ‖ξ‖ ^ (2 * γ - 1) * frequencyPair a h ‖ξ‖ ‖η‖ / bracket ‖η‖ := by
  unfold rowKernel
  rw [Real.rpow_sub_one (bracket_pos _).ne']
  have := (bracket_pos ‖ξ‖).ne'; have := (bracket_pos ‖η‖).ne'
  field_simp

/-- Global bound `⟨ξ⟩^{2γ}Φ_h ≤ 2` for `a < 1`, `2γ ≤ 1` (auxiliary to the Lean proof route). -/
theorem weighted_le_two {d : ℕ} {a γ : ℝ} (ha : a < 1) (hγ : 2 * γ ≤ 1) (h : ℝ) (ξ η : Rd d) :
    bracket ‖ξ‖ ^ (2 * γ) * rowKernel a h ξ η ≤ 2 := by
  rw [weighted_eq]
  have h1 : bracket ‖ξ‖ ^ (2 * γ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_bracket _) (by linarith)
  have h2 := frequencyPair_le_two ha h ‖ξ‖ ‖η‖
  have h3 := frequencyPair_nonneg a h ‖ξ‖ ‖η‖
  have h4 : 0 ≤ bracket ‖ξ‖ ^ (2 * γ - 1) := bracket_rpow_nonneg _ _
  rw [div_le_iff₀ (bracket_pos _)]
  have := one_le_bracket ‖η‖
  nlinarith [mul_le_mul h1 h2 h3 zero_le_one]

/-- Near-region shell bound (replaces the three-case bound of TeX l. 60-99): if `‖λ‖ ≤ 4‖ξ‖` and
`2^n ≤ ‖ξ - λ‖`, then `⟨ξ⟩^{2γ}Φ_h(ξ,ξ-λ) ≤ 2 (2^n/5)^{2γ-1} 2^{-n}` (auxiliary). -/
theorem weighted_le_near {d : ℕ} {a γ : ℝ} (ha : a < 1) (hγ : 2 * γ ≤ 1) (h : ℝ) (ξ l : Rd d)
    (n : ℕ) (hnear : ‖l‖ ≤ 4 * ‖ξ‖) (hn : (2 : ℝ) ^ n ≤ ‖ξ - l‖) :
    bracket ‖ξ‖ ^ (2 * γ) * rowKernel a h ξ (ξ - l) ≤
      2 * ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) * ((2 : ℝ) ^ n)⁻¹ := by
  rw [weighted_eq]
  have hη : ‖ξ - l‖ ≤ 5 * ‖ξ‖ := by linarith [norm_sub_le ξ l]
  have hp : (0 : ℝ) < 2 ^ n / 5 := by positivity
  have hξ : (2 : ℝ) ^ n / 5 ≤ bracket ‖ξ‖ := by
    have := abs_le_bracket ‖ξ‖; rw [abs_of_nonneg (norm_nonneg _)] at this
    linarith
  have h1 : bracket ‖ξ‖ ^ (2 * γ - 1) ≤ ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) :=
    Real.rpow_le_rpow_of_nonpos hp hξ (by linarith)
  have h2 := frequencyPair_le_two ha h ‖ξ‖ ‖ξ - l‖
  have h3 := frequencyPair_nonneg a h ‖ξ‖ ‖ξ - l‖
  have h4 : 0 ≤ bracket ‖ξ‖ ^ (2 * γ - 1) := bracket_rpow_nonneg _ _
  have h5 : (2 : ℝ) ^ n ≤ bracket ‖ξ - l‖ := by
    have := abs_le_bracket ‖ξ - l‖; rw [abs_of_nonneg (norm_nonneg _)] at this; linarith
  have h6 : 0 ≤ ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) := by positivity
  rw [div_le_iff₀ (bracket_pos _)]
  have hX : bracket ‖ξ‖ ^ (2 * γ - 1) * frequencyPair a h ‖ξ‖ ‖ξ - l‖ ≤
      2 * ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) := by nlinarith [mul_le_mul h1 h2 h3 h6]
  calc _ ≤ 2 * ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) := hX
    _ = 2 * ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) * ((2 : ℝ) ^ n)⁻¹ * 2 ^ n := by
        field_simp
    _ ≤ _ := by gcongr

/-- Far-region shell bound (TeX l. 101-113): if `4‖ξ‖ < ‖λ‖` and `2^n ≤ ‖λ‖`, then
`⟨ξ⟩^{2γ}Φ_h(ξ,ξ-λ) ≤ (4/3) 2^{-n} · 2 · 2^{1-a} ⟨h 2^n⟩^{a-1}` (auxiliary). -/
theorem weighted_le_far {d : ℕ} {a γ h : ℝ} (ha : a < 1) (hγ : 2 * γ ≤ 1) (h0 : 0 < h)
    (ξ l : Rd d) (n : ℕ) (hfar : 4 * ‖ξ‖ < ‖l‖) (hn : (2 : ℝ) ^ n ≤ ‖l‖) :
    bracket ‖ξ‖ ^ (2 * γ) * rowKernel a h ξ (ξ - l) ≤
      4 / 3 * ((2 : ℝ) ^ n)⁻¹ * (2 * (2 : ℝ) ^ (1 - a) * bracket (h * 2 ^ n) ^ (a - 1)) := by
  rw [weighted_eq]
  have hl : ‖l‖ ≤ ‖ξ‖ + ‖ξ - l‖ := by
    have := norm_sub_le ξ (ξ - l); simpa using this
  have hξ0 := norm_nonneg ξ
  have hη : 3 / 4 * ‖l‖ ≤ ‖ξ - l‖ := by linarith
  have hlpos : 0 < ‖l‖ := by linarith
  have hηpos : 0 < ‖ξ - l‖ := by linarith
  have ht : 0 ≤ h * 2 ^ n := by positivity
  have hQ : frequencyPair a h ‖ξ‖ ‖ξ - l‖ ≤ 2 * (2 : ℝ) ^ (1 - a) * bracket (h * 2 ^ n) ^ (a - 1) := by
    unfold frequencyPair
    have e1 := bracket_rpow_le_half ha ht (x := h * (‖ξ‖ - ‖ξ - l‖)) (by
      rw [abs_mul, abs_of_pos h0, abs_sub_comm]
      have : ‖l‖ / 2 ≤ |‖ξ - l‖ - ‖ξ‖| := by
        rw [abs_of_nonneg (by linarith)]; linarith
      have : (2 : ℝ) ^ n / 2 ≤ |‖ξ - l‖ - ‖ξ‖| := by linarith
      nlinarith)
    have e2 := bracket_rpow_le_half ha ht (x := h * (‖ξ‖ + ‖ξ - l‖)) (by
      rw [abs_mul, abs_of_pos h0, abs_of_nonneg (by positivity)]
      nlinarith)
    linarith
  have h1 : bracket ‖ξ‖ ^ (2 * γ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_bracket _) (by linarith)
  have h3 := frequencyPair_nonneg a h ‖ξ‖ ‖ξ - l‖
  have h4 : 0 ≤ bracket ‖ξ‖ ^ (2 * γ - 1) := bracket_rpow_nonneg _ _
  have h5 : 3 / 4 * (2 : ℝ) ^ n ≤ bracket ‖ξ - l‖ := by
    have := abs_le_bracket ‖ξ - l‖; rw [abs_of_nonneg (norm_nonneg _)] at this; linarith
  have hK : 0 ≤ 2 * (2 : ℝ) ^ (1 - a) * bracket (h * 2 ^ n) ^ (a - 1) := by
    have := bracket_rpow_nonneg (a - 1) (h * 2 ^ n); positivity
  have hX : bracket ‖ξ‖ ^ (2 * γ - 1) * frequencyPair a h ‖ξ‖ ‖ξ - l‖ ≤
      2 * (2 : ℝ) ^ (1 - a) * bracket (h * 2 ^ n) ^ (a - 1) := by
    nlinarith [mul_le_mul h1 hQ h3 zero_le_one]
  rw [div_le_iff₀ (bracket_pos _)]
  calc _ ≤ 2 * (2 : ℝ) ^ (1 - a) * bracket (h * 2 ^ n) ^ (a - 1) := hX
    _ = 4 / 3 * ((2 : ℝ) ^ n)⁻¹ * (2 * (2 : ℝ) ^ (1 - a) * bracket (h * 2 ^ n) ^ (a - 1)) *
          (3 / 4 * 2 ^ n) := by field_simp
    _ ≤ _ := by gcongr


/-! ### Assembly -/

/-- Near-shell coefficients (auxiliary to the Lean proof route). -/
def nearCoef (γ : ℝ) : ℕ → ℝ
  | 0 => 2
  | n + 1 => 2 * ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) * ((2 : ℝ) ^ n)⁻¹

/-- Far-shell coefficients (auxiliary to the Lean proof route). -/
def farCoef (a h : ℝ) : ℕ → ℝ
  | 0 => 2
  | n + 1 => 4 / 3 * ((2 : ℝ) ^ n)⁻¹ * (2 * (2 : ℝ) ^ (1 - a) * bracket (h * 2 ^ n) ^ (a - 1))

/-- Near coefficients are nonnegative (auxiliary to the Lean proof route). -/
theorem nearCoef_nonneg (γ : ℝ) (j : ℕ) : 0 ≤ nearCoef γ j := by
  cases j <;> simp only [nearCoef] <;> positivity

/-- Far coefficients are nonnegative (auxiliary to the Lean proof route). -/
theorem farCoef_nonneg (a h : ℝ) (j : ℕ) : 0 ≤ farCoef a h j := by
  cases j with
  | zero => simp [farCoef]
  | succ n => simp only [farCoef]; have := bracket_rpow_nonneg (a - 1) (h * 2 ^ n); positivity

/-- Pointwise two-centre shell majorant of the weighted kernel (auxiliary). -/
theorem weighted_le_shells {d : ℕ} {a γ h : ℝ} (ha : a < 1) (hγ : 2 * γ ≤ 1) (h0 : 0 < h)
    (ξ l : Rd d) :
    ENNReal.ofReal (bracket ‖ξ‖ ^ (2 * γ) * rowKernel a h ξ (ξ - l)) ≤
      (∑' j, (closedBall ξ ((2 : ℝ) ^ j)).indicator (fun _ => ENNReal.ofReal (nearCoef γ j)) l) +
      ∑' j, (closedBall (0 : Rd d) ((2 : ℝ) ^ j)).indicator
        (fun _ => ENNReal.ofReal (farCoef a h j)) l := by
  by_cases hnear : ‖l‖ ≤ 4 * ‖ξ‖
  · refine le_trans ?_ le_self_add
    apply le_shellSum
    · intro _; exact ENNReal.ofReal_le_ofReal (by simpa [nearCoef] using weighted_le_two ha hγ h ξ _)
    · intro n hn _
      rw [norm_sub_rev] at hn
      exact ENNReal.ofReal_le_ofReal (weighted_le_near ha hγ h ξ l n hnear hn)
  · refine le_trans ?_ le_add_self
    apply le_shellSum
    · intro _; exact ENNReal.ofReal_le_ofReal (by simpa [farCoef] using weighted_le_two ha hγ h ξ _)
    · intro n hn _
      rw [sub_zero] at hn
      exact ENNReal.ofReal_le_ofReal (weighted_le_far ha hγ h0 ξ l n (not_le.mp hnear) hn)

/-- Main estimate in pointwise form: there is `K = K(α,a,γ)`, chosen before `d, ν, C, h, ξ`,
with `J_h(ξ) ≤ K C B_α(h)`. Hypotheses: `a < 1`, `α + a < 2`, `2γ ≤ 1`, `α + 2γ < 2`, `C ≥ 0`,
and the open-ball growth `ν(B(y,r)) ≤ C r^α` for all `y` and `r > 0`; `ν` is any measure. -/
theorem rowIntegral_le {α a γ : ℝ} (ha : a < 1) (hαa : α + a < 2) (hγ : 2 * γ ≤ 1)
    (hαγ : α + 2 * γ < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℕ) (ν : Measure (Rd d)) (C : ℝ), 0 ≤ C →
      (∀ y : Rd d, ∀ r : ℝ, 0 < r → ν (ball y r) ≤ ENNReal.ofReal (C * r ^ α)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ ξ : Rd d,
        rowIntegral a γ h ν ξ ≤ ENNReal.ofReal (K * C * scaleProfile α h) := by
  obtain ⟨KS, hKS0, hKS⟩ := rowSeries_tsum_le ha hαa
  set A : ℝ := (2 : ℝ) ^ α with hA
  have hA0 : 0 < A := by positivity
  set ρN : ℝ := (2 : ℝ) ^ (2 * γ - 1) * 2⁻¹ * A with hρN
  have hρN : ρN = (2 : ℝ) ^ (α + 2 * γ - 2) := by
    rw [hρN, hA, show α + 2 * γ - 2 = (2 * γ - 1) + -1 + α by ring,
      Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_neg_one]
  have hρN1 : ρN < 1 := by rw [hρN]; exact two_rpow_lt_one (by linarith)
  have hρN0 : 0 < ρN := by positivity
  set KN : ℝ := 2 + 2 * (5 : ℝ) ^ (1 - 2 * γ) * A * (1 - ρN)⁻¹ with hKN
  have hKN0 : 0 ≤ KN := by have := inv_nonneg.mpr (show (0:ℝ) ≤ 1 - ρN by linarith); positivity
  set KF : ℝ := 8 / 3 * (2 : ℝ) ^ (1 - a) * A with hKF
  have hKF0 : 0 ≤ KF := by positivity
  refine ⟨2 + KN + KF * KS, by positivity, ?_⟩
  intro d ν C hC hgrowth h h0 h1 ξ
  have hB1 := one_le_scaleProfile α h0 h1
  -- move the weight inside
  have hJ : rowIntegral a γ h ν ξ =
      ∫⁻ l, ENNReal.ofReal (bracket ‖ξ‖ ^ (2 * γ) * rowKernel a h ξ (ξ - l)) ∂ν := by
    unfold rowIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext l
    rw [ENNReal.ofReal_mul (bracket_rpow_nonneg _ _)]
  rw [hJ]
  -- shell decomposition
  have hmeas : ∀ (y : Rd d) (c : ℕ → ℝ), Measurable fun l : Rd d =>
      ∑' j, (closedBall y ((2 : ℝ) ^ j)).indicator (fun _ => ENNReal.ofReal (c j)) l :=
    fun y c => Measurable.tsum fun j => measurable_const.indicator measurableSet_closedBall
  have hsplit := lintegral_mono (μ := ν) fun l => weighted_le_shells (γ := γ) ha hγ h0 ξ l
  rw [lintegral_add_left (hmeas ξ _), lintegral_shellSum, lintegral_shellSum] at hsplit
  have hN := shellSum_le ν hgrowth ξ (nearCoef γ) (nearCoef_nonneg γ)
  have hF := shellSum_le ν hgrowth 0 (farCoef a h) (farCoef_nonneg a h)
  -- near series
  have hNs : ∑' j, ENNReal.ofReal (nearCoef γ j * C * A ^ j) ≤
      ENNReal.ofReal (2 * C) + ENNReal.ofReal (2 * (5 : ℝ) ^ (1 - 2 * γ) * A * C * (1 - ρN)⁻¹) := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [nearCoef, pow_zero, mul_one]
    gcongr
    have hterm : ∀ n : ℕ, 2 * ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) * ((2 : ℝ) ^ n)⁻¹ * C * A ^ (n + 1) =
        2 * (5 : ℝ) ^ (1 - 2 * γ) * A * C * ρN ^ n := by
      intro n
      have e : ((2 : ℝ) ^ n / 5) ^ (2 * γ - 1) = ((2 : ℝ) ^ (2 * γ - 1)) ^ n * (5 : ℝ) ^ (1 - 2 * γ) := by
        rw [Real.div_rpow (by positivity) (by norm_num), two_pow_rpow, div_eq_mul_inv,
          ← Real.rpow_neg (by norm_num), neg_sub]
      rw [e, ← inv_pow, show ρN = (2 : ℝ) ^ (2 * γ - 1) * 2⁻¹ * A from rfl]
      ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one hρN0.le hρN1).mul_left _), tsum_mul_left,
      tsum_geometric_of_lt_one hρN0.le hρN1]
  -- far series
  have hFs : ∑' j, ENNReal.ofReal (farCoef a h j * C * A ^ j) ≤
      ENNReal.ofReal (2 * C) + ENNReal.ofReal (KF * C * ∑' n, rowSeries α a h n) := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [farCoef, pow_zero, mul_one]
    gcongr
    have hterm : ∀ n : ℕ, 4 / 3 * ((2 : ℝ) ^ n)⁻¹ *
        (2 * (2 : ℝ) ^ (1 - a) * bracket (h * 2 ^ n) ^ (a - 1)) * C * A ^ (n + 1) =
        KF * C * rowSeries α a h n := by
      intro n
      have e : (2 : ℝ) ^ (α - 1) = A * 2⁻¹ := by
        rw [Real.rpow_sub_one (by norm_num), div_eq_mul_inv]
      rw [hKF, rowSeries, e, ← inv_pow]
      ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (mul_nonneg hKF0 hC) (rowSeries_nonneg α a h n))
      ((summable_rowSeries ha hαa h0).mul_left _), tsum_mul_left]
  have hS := hKS h h0 h1
  have hS0 : 0 ≤ ∑' n, rowSeries α a h n := tsum_nonneg (rowSeries_nonneg α a h)
  calc _ ≤ _ := hsplit
    _ ≤ _ := add_le_add (hN.trans hNs) (hF.trans hFs)
    _ = ENNReal.ofReal (2 * C + 2 * (5 : ℝ) ^ (1 - 2 * γ) * A * C * (1 - ρN)⁻¹ +
          (2 * C + KF * C * ∑' n, rowSeries α a h n)) := by
        have := inv_nonneg.mpr (show (0:ℝ) ≤ 1 - ρN by linarith)
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : 2 * C + 2 * (5 : ℝ) ^ (1 - 2 * γ) * A * C * (1 - ρN)⁻¹ = KN * C := by
          rw [hKN]; ring
        rw [e1]
        have hKS' : KF * C * ∑' n, rowSeries α a h n ≤ KF * C * (KS * scaleProfile α h) := by
          gcongr
        have : 0 ≤ KN * C := by positivity
        have : 0 ≤ KF * KS * C := by positivity
        nlinarith


/-- `P:frequency-row` (TeX l. 47-55), general form: under `a < 1`, `α + a < 2`, `2γ ≤ 1`,
`α + 2γ < 2`, there is `K ≥ 0`, chosen before `d, ν, C, h` (so independent of them), such that
for every measure `ν` on `ℝ^d` with `ν(B(y,r)) ≤ C r^α` (open balls, all `y`, `r > 0`) and
`C ≥ 0`, and every `0 < h ≤ 1`: `sup_ξ J_h(ξ) ≤ K C B_α(h)`; moreover for every `ξ` the kernel
`λ ↦ Φ_h(ξ, ξ-λ)` is `ν`-integrable and `⟨ξ⟩^{2γ} ∫ Φ_h(ξ,ξ-λ) ν(dλ) ≤ K C B_α(h)`. -/
theorem frequency_row {α a γ : ℝ} (ha : a < 1) (hαa : α + a < 2) (hγ : 2 * γ ≤ 1)
    (hαγ : α + 2 * γ < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℕ) (ν : Measure (Rd d)) (C : ℝ), 0 ≤ C →
      (∀ y : Rd d, ∀ r : ℝ, 0 < r → ν (ball y r) ≤ ENNReal.ofReal (C * r ^ α)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        (⨆ ξ, rowIntegral a γ h ν ξ) ≤ ENNReal.ofReal (K * C * scaleProfile α h) ∧
        ∀ ξ : Rd d, Integrable (fun l => rowKernel a h ξ (ξ - l)) ν ∧
          bracket ‖ξ‖ ^ (2 * γ) * ∫ l, rowKernel a h ξ (ξ - l) ∂ν ≤ K * C * scaleProfile α h := by
  obtain ⟨K, hK0, hK⟩ := rowIntegral_le ha hαa hγ hαγ
  refine ⟨K, hK0, fun d ν C hC hgrowth h h0 h1 => ⟨iSup_le fun ξ => hK d ν C hC hgrowth h h0 h1 ξ,
    fun ξ => ?_⟩⟩
  have hJ := hK d ν C hC hgrowth h h0 h1 ξ
  have hB := one_le_scaleProfile α h0 h1
  have hfin : ∫⁻ l, ENNReal.ofReal (rowKernel a h ξ (ξ - l)) ∂ν ≠ ⊤ := by
    intro htop
    have hw : ENNReal.ofReal (bracket ‖ξ‖ ^ (2 * γ)) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; exact Real.rpow_pos_of_pos (bracket_pos _) _
    have : rowIntegral a γ h ν ξ = ⊤ := by
      unfold rowIntegral; rw [htop, ENNReal.mul_top hw]
    rw [this] at hJ; exact ENNReal.ofReal_ne_top (top_le_iff.mp hJ)
  have hmeas : AEStronglyMeasurable (fun l => rowKernel a h ξ (ξ - l)) ν :=
    (continuous_rowKernel a h ξ).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[ν] fun l => rowKernel a h ξ (ξ - l) :=
    Filter.Eventually.of_forall fun l => rowKernel_nonneg a h ξ _
  refine ⟨⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_top_iff_ne_top.mpr hfin)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  have e : bracket ‖ξ‖ ^ (2 * γ) * (∫⁻ l, ENNReal.ofReal (rowKernel a h ξ (ξ - l)) ∂ν).toReal =
      (rowIntegral a γ h ν ξ).toReal := by
    unfold rowIntegral
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (bracket_rpow_nonneg _ _)]
  rw [e]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hJ

/-- The time-scale step of `C:frequency-time` (TeX l. 155-163), auxiliary scalar form:
for `2β < 2 - a` and `2β < 3 - a - α` there is `c ≥ 0` with `h^{2-a} B_α(h) ≤ c h^{2β}`
for `0 < h ≤ 1`. -/
theorem scale_time_le {α a β : ℝ} (hβa : 2 * β < 2 - a) (hβα : 2 * β < 3 - a - α) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      h ^ (2 - a) * scaleProfile α h ≤ c * h ^ (2 * β) := by
  rcases lt_trichotomy α 1 with hα | hα | hα
  · refine ⟨1, zero_le_one, fun h h0 h1 => ?_⟩
    simp only [scaleProfile, hα, ite_true, mul_one, one_mul]
    exact Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)
  · subst hα
    set δ : ℝ := 2 - a - 2 * β with hδ
    have hδ0 : 0 < δ := by linarith
    refine ⟨1 + Real.exp (-1) / δ, by positivity, fun h h0 h1 => ?_⟩
    simp only [scaleProfile, lt_irrefl, ite_false, ite_true]
    set u : ℝ := Real.log (1 / h) with hu
    have hu0 : 0 ≤ u := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
    have hhd : h ^ δ = Real.exp (-(δ * u)) := by
      rw [Real.rpow_def_of_pos h0, hu, one_div, Real.log_inv]; ring_nf
    have hsplit : h ^ (2 - a) = h ^ (2 * β) * h ^ δ := by
      rw [← Real.rpow_add h0]; congr 1; rw [hδ]; ring
    have ht : δ * u * Real.exp (-(δ * u)) ≤ Real.exp (-1) := by
      have := Real.add_one_le_exp (δ * u - 1)
      have e : Real.exp (δ * u - 1) * Real.exp (-(δ * u)) = Real.exp (-1) := by
        rw [← Real.exp_add]; ring_nf
      calc δ * u * Real.exp (-(δ * u)) ≤ Real.exp (δ * u - 1) * Real.exp (-(δ * u)) := by
            gcongr; linarith
        _ = _ := e
    have hE : Real.exp (-(δ * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hu' : u * Real.exp (-(δ * u)) ≤ Real.exp (-1) / δ := by
      rw [le_div_iff₀ hδ0]; nlinarith
    have hp : 0 < h ^ (2 * β) := Real.rpow_pos_of_pos h0 _
    rw [hsplit, hhd]
    have : Real.exp (-(δ * u)) * (1 + u) ≤ 1 + Real.exp (-1) / δ := by nlinarith
    calc h ^ (2 * β) * Real.exp (-(δ * u)) * (1 + u)
        = h ^ (2 * β) * (Real.exp (-(δ * u)) * (1 + u)) := by ring
      _ ≤ h ^ (2 * β) * (1 + Real.exp (-1) / δ) := by gcongr
      _ = _ := by ring
  · refine ⟨1, zero_le_one, fun h h0 h1 => ?_⟩
    simp only [scaleProfile, not_lt.mpr hα.le, hα.ne', ite_false, one_mul]
    rw [← Real.rpow_add h0]
    exact Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)

/-- `C:frequency-time` (TeX l. 141-165), general form: for `2β < 2 - a` and
`2β < 3 - a - α` (and the hypotheses of `frequency_row`) there is `K_β ≥ 0`, chosen before
`d, ν, C, h`, with `h^{2-a} sup_ξ J_h(ξ) ≤ K_β C h^{2β}` for `0 < h ≤ 1`. -/
theorem frequency_time {α a γ β : ℝ} (ha : a < 1) (hαa : α + a < 2) (hγ : 2 * γ ≤ 1)
    (hαγ : α + 2 * γ < 2) (hβa : 2 * β < 2 - a) (hβα : 2 * β < 3 - a - α) :
    ∃ Kβ : ℝ, 0 ≤ Kβ ∧ ∀ (d : ℕ) (ν : Measure (Rd d)) (C : ℝ), 0 ≤ C →
      (∀ y : Rd d, ∀ r : ℝ, 0 < r → ν (ball y r) ≤ ENNReal.ofReal (C * r ^ α)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        ENNReal.ofReal (h ^ (2 - a)) * (⨆ ξ, rowIntegral a γ h ν ξ) ≤
          ENNReal.ofReal (Kβ * C * h ^ (2 * β)) := by
  obtain ⟨K, hK0, hK⟩ := frequency_row ha hαa hγ hαγ
  obtain ⟨c, hc0, hc⟩ := scale_time_le (α := α) hβa hβα
  refine ⟨K * c, mul_nonneg hK0 hc0, fun d ν C hC hgrowth h h0 h1 => ?_⟩
  have hB := one_le_scaleProfile α h0 h1
  calc ENNReal.ofReal (h ^ (2 - a)) * (⨆ ξ, rowIntegral a γ h ν ξ)
      ≤ ENNReal.ofReal (h ^ (2 - a)) * ENNReal.ofReal (K * C * scaleProfile α h) := by
        gcongr; exact (hK d ν C hC hgrowth h h0 h1).1
    _ = ENNReal.ofReal (K * C * (h ^ (2 - a) * scaleProfile α h)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have := hc h h0 h1
        calc K * C * (h ^ (2 - a) * scaleProfile α h) ≤ K * C * (c * h ^ (2 * β)) := by gcongr
          _ = _ := by ring

/-! ### Exact-hypothesis wrappers -/

/-- `P:frequency-row` with the manuscript's hypotheses (TeX l. 3-55): the section retains
`H:homog` with `a = α₀` (some `Γ, μ` on `ℝ^d`), fixes `0 < γ < min(1/2, (2-α)/2)`
(`E:variance-gamma-range`), and takes a positive Radon measure `ν` on `ℝ^d` with
`ν(B(y,r)) ≤ C r^α` (`E:frequency-translated-growth`, open balls), `C ≥ 0`. The constant `K`
depends only on `α, a, γ`: it is chosen before `d, Γ, μ, ν, C, h, ξ`. -/
theorem frequency_row_paper {α a γ : ℝ} (_hγ0 : 0 < γ) (hγ : γ < min (1 / 2) ((2 - α) / 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℕ) (Γ μ : Measure (Rd d)), HomogCovariance d α a Γ μ →
      ∀ ν : Measure (Rd d), IsLocallyFiniteMeasure ν → ∀ C : ℝ, 0 ≤ C →
      (∀ y : Rd d, ∀ r : ℝ, 0 < r → ν (ball y r) ≤ ENNReal.ofReal (C * r ^ α)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        (⨆ ξ, rowIntegral a γ h ν ξ) ≤ ENNReal.ofReal (K * C * scaleProfile α h) ∧
        ∀ ξ : Rd d, Integrable (fun l => rowKernel a h ξ (ξ - l)) ν ∧
          bracket ‖ξ‖ ^ (2 * γ) * ∫ l, rowKernel a h ξ (ξ - l) ∂ν ≤ K * C * scaleProfile α h := by
  rw [lt_min_iff] at hγ
  by_cases hnum : a < 1 ∧ α + a < 2
  · obtain ⟨K, hK0, hK⟩ := frequency_row (γ := γ) hnum.1 hnum.2 (by linarith) (by linarith)
    exact ⟨K, hK0, fun d _ _ _ ν _ C hC hg h h0 h1 => hK d ν C hC hg h h0 h1⟩
  · refine ⟨0, le_rfl, fun d Γ μ hH => ?_⟩
    exact absurd ⟨hH.alpha0_lt_one, by linarith [hH.threshold]⟩ hnum

/-- `C:frequency-time` with the manuscript's hypotheses (TeX l. 141-150, with the standing
hypotheses of `frequency_row_paper`): for every `β` with
`1/2 < β < min(1 - a/2, (3 - a - α)/2)` (`E:variance-beta-range`) there is a finite
`K_β = K_β(α,a,γ,β)`, chosen before `d, Γ, μ, ν, C, h`, with
`h^{2-a} sup_ξ J_h(ξ) ≤ K_β C h^{2β}` for `0 < h ≤ 1`. -/
theorem frequency_time_paper {α a γ : ℝ} (_hγ0 : 0 < γ) (hγ : γ < min (1 / 2) ((2 - α) / 2))
    (β : ℝ) (_hβ0 : 1 / 2 < β) (hβ : β < min (1 - a / 2) ((3 - a - α) / 2)) :
    ∃ Kβ : ℝ, 0 ≤ Kβ ∧ ∀ (d : ℕ) (Γ μ : Measure (Rd d)), HomogCovariance d α a Γ μ →
      ∀ ν : Measure (Rd d), IsLocallyFiniteMeasure ν → ∀ C : ℝ, 0 ≤ C →
      (∀ y : Rd d, ∀ r : ℝ, 0 < r → ν (ball y r) ≤ ENNReal.ofReal (C * r ^ α)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        ENNReal.ofReal (h ^ (2 - a)) * (⨆ ξ, rowIntegral a γ h ν ξ) ≤
          ENNReal.ofReal (Kβ * C * h ^ (2 * β)) := by
  rw [lt_min_iff] at hγ hβ
  by_cases hnum : a < 1 ∧ α + a < 2
  · obtain ⟨K, hK0, hK⟩ := frequency_time (γ := γ) (β := β) hnum.1 hnum.2 (by linarith) (by linarith)
      (by linarith) (by linarith)
    exact ⟨K, hK0, fun d _ _ _ ν _ C hC hg h h0 h1 => hK d ν C hC hg h h0 h1⟩
  · refine ⟨0, le_rfl, fun d Γ μ hH => ?_⟩
    exact absurd ⟨hH.alpha0_lt_one, by linarith [hH.threshold]⟩ hnum

end StratonovichHAMSecondMoment.FrequencyRow
