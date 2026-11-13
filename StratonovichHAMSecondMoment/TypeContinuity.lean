module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Section `S:temporal-type-continuity` (Temporal interpolation of the full
moment) of `notes/notes_stratonovich_ham_second_moment.tex` (main TeX file;
line numbers at revision a284420), together with the lemma it uses from the
preceding section `S:near-static-lower`:

* `L:positive-series-type` (Type of a positive coefficient series; lines
  7222-7234, proof 7236-7263): formalized IN FULL with the manuscript's
  hypotheses (`positive_series_type_paper`), nothing supplied. The type
  `τ = limsup z^{-1/ν} log F(z)` is an extended real (`seriesType`, no
  truncation), the coefficient type `K = limsup ((k!)^ν c_k)^{1/k}` is in
  `ℝ≥0∞` (`coeffType`; its terms are nonnegative reals, so `ofReal` does not
  truncate them); "`F(z) < ∞` for `z ≥ 0`" is summability. Proof route as in
  the TeX, with two differences recorded at the lemmas: the first half uses
  the eventual bound `F(z) ≤ e^{L z^{1/ν}}` instead of the global
  `C_L e^{L z^{1/ν}}`, and the factorial bounds are proved by induction
  (`SeriesType.log_factorial_bounds`) instead of integrating `log x`.
* `P:moment-growth-logconvex` (Log-convexity of the upper growth type; lines
  7516-7528, proof 7530-7572): every conclusion is proved
  (`moment_growth_logconvex_paper`): positivity and finiteness of
  `Λ̄_p` on `[0, a_max)`, `E:moment-growth-logconvex`, convexity of
  `log Λ̄_p` (on `[0, a_max)`, the range of the inequality) and continuity of
  `Λ̄_p` and `log Λ̄_p` on `(0, a_max)` (via
  `ConvexOn.continuousOn_interior`, instead of the TeX's secant slopes).
  The identification of the type of `F_{p,a}` with `Λ̄_p(a)` through
  `z = T^{β(a)}` is PROVED (`growthUpper_eq_seriesType`). Supplied as named
  inputs (`TypeContinuityInputs`, each no stronger than its source):
  `E:full-moment-positive-series` and `E:full-moment-coefficient-holder`
  (`L:full-moment-coefficient-holder`, whose proof needs the stochastic
  diagram analysis), the static law `E:static-ratio-input` (Chen-Hu),
  `E:static-minorant-rate` (`P:static-minorant-lower`),
  `E:full-upper-bound` (`T:full-upper`) at each exponent `a`, and the
  Cauchy-Schwarz inequality `(E u)^2 ≤ E u^2`. Positivity and finiteness of
  the rates are derived from these exactly as in the TeX proof (lines
  7531-7537), not supplied.
* `C:static-moment-constant-continuity` (Recovery of the static moment
  constant; lines 7574-7593, proof 7595-7606): every conclusion is proved
  (`static_moment_constant_continuity_paper`) from the same inputs (the
  corollary's own inputs `P:static-minorant-lower` and `Λ̄_p(0) = C_p` are
  derived from `minorant` and `static_law`).

Modelling choices: `E[u^{(a)}(T,x)^p]` is an abstract real function
`mom p a T` at a fixed point `x` (so the spatial stationarity used at line
7541 is not needed); `mom p 0` is the static moment `E[U(T,x)^p]`, as the TeX
defines `u^{(0)} = U` (lines 7072-7074). Growth rates are extended reals
(`growthUpper`, `growthLower`); statements about `Λ̄_p` as real numbers use
`EReal.toReal` only together with a proved finiteness (and positivity), so no
junk value of `toReal` enters. The section's standing assumption "a nonzero
spatial covariance in `H:homog`" (lines 7062, 7423) is carried as
`HomogCovariance` and `Γ ≠ 0`; the proofs use from it only `α < 2` (hence
`ν = 3 - α ≥ 1`, `a_max > 0`, `β(a) > 0`), and `Γ ≠ 0` is carried unused.
The general cores (`growth_logconvex_core`, `static_constant_core`) state
the arguments for an arbitrary family with positivity and finiteness of the
rates as hypotheses. Helpers marked "Auxiliary (Lean route)" serve only the
Lean proof and are not TeX steps.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SeriesType
public import StratonovichHAMSecondMoment.HomogHypothesis

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real Filter Topology Set
open scoped Nat ENNReal

namespace StratonovichHAMSecondMoment.TypeContinuity

/-! ### Auxiliary: extended-real limsup bounds of real functions -/

/-- Auxiliary (Lean route): if for every `ε > 0` eventually `f ≤ B + ε`, then
the extended-real limsup of `f` is at most `B`. -/
theorem limsup_le_of_eventually_le_add {α : Type*} {l : Filter α} (f : α → ℝ) (B : ℝ)
    (h : ∀ ε > 0, ∀ᶠ x in l, f x ≤ B + ε) :
    limsup (fun x => (f x : EReal)) l ≤ (B : EReal) := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨x, hBx, hxl⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hBx' : B < x := EReal.coe_lt_coe_iff.1 hBx
  have hle : limsup (fun x => (f x : EReal)) l ≤ ((B + (x - B) : ℝ) : EReal) :=
    limsup_le_of_le (by isBoundedDefault)
      ((h (x - B) (by linarith)).mono fun y hy => EReal.coe_le_coe_iff.2 hy)
  rw [show B + (x - B) = x by ring] at hle
  exact absurd hxl (not_lt.2 hle)

/-- Auxiliary (Lean route): a strict upper bound on the extended-real limsup of
`f` holds eventually for `f`. -/
theorem eventually_lt_of_limsup_lt_coe {α : Type*} {l : Filter α} (f : α → ℝ) (L : ℝ)
    (h : limsup (fun x => (f x : EReal)) l < (L : EReal)) : ∀ᶠ x in l, f x < L :=
  (eventually_lt_of_limsup_lt h (by isBoundedDefault)).mono fun _ hx =>
    EReal.coe_lt_coe_iff.1 hx

/-! ### `L:positive-series-type`: definitions -/

/-- The power series `F(z) = ∑_{k ≥ 0} c_k z^k` (a Lean `tsum`; it is the
manuscript's value whenever the family is summable, which is a hypothesis of
every result below for `z ≥ 0`). -/
def seriesSum (c : ℕ → ℝ) (z : ℝ) : ℝ := ∑' k : ℕ, c k * z ^ k

/-- The normalized logarithmic type
`τ = limsup_{z → ∞} z^{-1/ν} log F(z)` of `L:positive-series-type` (main TeX
line 7226), as an extended real number (no truncation, no boundedness side
condition). -/
def seriesType (ν : ℝ) (c : ℕ → ℝ) : EReal :=
  limsup (fun z : ℝ => ((z ^ (-(1 / ν)) * Real.log (seriesSum c z) : ℝ) : EReal)) atTop

/-- The coefficient type `K = limsup_{k → ∞} ((k!)^ν c_k)^{1/k}` of
`E:positive-series-type` (main TeX line 7230), in `ℝ≥0∞`. For `c_k ≥ 0` (a
hypothesis of every result below) the real number `((k!)^ν c_k)^{1/k}` is
nonnegative, so `ENNReal.ofReal` does not truncate it; `K = ∞` is allowed.
The `k = 0` term (where Lean's `1/0 = 0` gives the value `1`) does not affect
the limsup. -/
def coeffType (ν : ℝ) (c : ℕ → ℝ) : ℝ≥0∞ :=
  limsup (fun k : ℕ => ENNReal.ofReal (((k ! : ℝ) ^ ν * c k) ^ ((1 : ℝ) / k))) atTop

/-- Auxiliary (Lean route): with `c_0 = 1`, `c_k ≥ 0` and summability at `z ≥ 0`,
`F(z) ≥ 1`, so `log F(z) ≥ 0` (the TeX's "`τ ≥ 0` since `c_0 = 1`"). -/
theorem one_le_seriesSum {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (hc0 : c 0 = 1) {z : ℝ}
    (hz : 0 ≤ z) (hs : Summable (fun k => c k * z ^ k)) : 1 ≤ seriesSum c z := by
  have := hs.le_tsum 0 (fun j _ => mul_nonneg (hc j) (pow_nonneg hz j))
  simpa [seriesSum, hc0] using this

/-- Auxiliary (Lean route): each term `c_k z^k` is at most `F(z)`. -/
theorem term_le_seriesSum {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) {z : ℝ} (hz : 0 ≤ z)
    (hs : Summable (fun k => c k * z ^ k)) (k : ℕ) : c k * z ^ k ≤ seriesSum c z :=
  hs.le_tsum k (fun j _ => mul_nonneg (hc j) (pow_nonneg hz j))

/-- The type is nonnegative: `0 ≤ τ` (main TeX line 7237, "Since `c_0 = 1`,
`τ ≥ 0`"). -/
theorem seriesType_nonneg {ν : ℝ} {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (hc0 : c 0 = 1)
    (hF : ∀ z, 0 ≤ z → Summable (fun k => c k * z ^ k)) : 0 ≤ seriesType ν c := by
  refine le_limsup_of_frequently_le (Eventually.frequently ?_) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
  exact EReal.coe_nonneg.2 (mul_nonneg (Real.rpow_nonneg hz _)
    (Real.log_nonneg (one_le_seriesSum hc hc0 hz (hF z hz))))

/-! ### `L:positive-series-type`: the two inequalities -/

/-- Auxiliary (Lean route): `(log k + 1)/k → 0` along the natural numbers. -/
theorem tendsto_log_add_one_div_nat :
    Tendsto (fun k : ℕ => (Real.log k + 1) / k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero
  have h3 := (h1.add h2).comp tendsto_natCast_atTop_atTop
  rw [add_zero] at h3
  refine h3.congr fun k => ?_
  simp [add_div]

/-- **First half of `L:positive-series-type`** (main TeX lines 7237-7249): if
`τ < L` then `K ≤ (L/ν)^ν`. Needs only `ν > 0`. Route as in the TeX
(test the single term `c_k z^k ≤ F(z)` at `z = (νk/L)^ν` and use the upper
factorial bound `log k! ≤ k log k - k + 1 + log k`), except that the TeX's
global bound `F(z) ≤ C_L e^{L z^{1/ν}}` for all `z ≥ 0` is replaced by the
eventual bound, which suffices since `(νk/L)^ν → ∞`. -/
theorem coeffType_le_of_seriesType_lt {ν : ℝ} (hν : 0 < ν) {c : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hc0 : c 0 = 1)
    (hF : ∀ z, 0 ≤ z → Summable (fun k => c k * z ^ k)) (L : ℝ)
    (hL : seriesType ν c < (L : EReal)) :
    coeffType ν c ≤ ENNReal.ofReal ((L / ν) ^ ν) := by
  have hev := eventually_lt_of_limsup_lt_coe _ L hL
  obtain ⟨Z0, hZ0⟩ := eventually_atTop.1 hev
  -- `L > 0`
  have hLpos : 0 < L := by
    set z := max Z0 1
    have hz1 : (1 : ℝ) ≤ z := le_max_right _ _
    have hz0 : (0 : ℝ) ≤ z := by linarith
    have := hZ0 z (le_max_left _ _)
    have hnn : 0 ≤ z ^ (-(1 / ν)) * Real.log (seriesSum c z) :=
      mul_nonneg (Real.rpow_nonneg hz0 _)
        (Real.log_nonneg (one_le_seriesSum hc hc0 hz0 (hF z hz0)))
    linarith
  -- the test points `z_k = (ν k / L)^ν` tend to infinity
  have hzk : Tendsto (fun k : ℕ => (ν * k / L) ^ ν) atTop atTop := by
    have : Tendsto (fun k : ℕ => ν * (k : ℝ) / L) atTop atTop := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hν
      exact h.atTop_div_const hLpos
    exact (tendsto_rpow_atTop hν).comp this
  set g : ℕ → ℝ := fun k => Real.exp (ν * ((Real.log k + 1) / k)) * (L / ν) ^ ν with hg
  have hgt : Tendsto g atTop (𝓝 ((L / ν) ^ ν)) := by
    have h0 : Tendsto (fun k : ℕ => Real.exp (ν * ((Real.log k + 1) / k))) atTop (𝓝 1) := by
      have := ((tendsto_log_add_one_div_nat.const_mul ν).comp tendsto_id).rexp
      simpa using this
    simpa [hg] using h0.mul_const ((L / ν) ^ ν)
  have hbound : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (((k ! : ℝ) ^ ν * c k) ^ ((1 : ℝ) / k)) ≤ ENNReal.ofReal (g k) := by
    filter_upwards [hzk.eventually_ge_atTop Z0, eventually_ge_atTop 1] with k hk hk1
    refine ENNReal.ofReal_le_ofReal ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hfact : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    set z := (ν * k / L) ^ ν with hzdef
    have hbase : 0 < ν * k / L := by positivity
    have hz0 : 0 < z := Real.rpow_pos_of_pos hbase _
    have hgpos : 0 < g k := by positivity
    rcases (hc k).eq_or_lt with hck | hck
    · rw [← hck, mul_zero, Real.zero_rpow (by positivity)]
      exact hgpos.le
    -- `log F(z) < ν k`
    have hlogF : Real.log (seriesSum c z) < ν * k := by
      have h1 := hZ0 z hk
      have hzr : z ^ (1 / ν) = ν * k / L := by
        rw [hzdef, one_div, Real.rpow_rpow_inv hbase.le hν.ne']
      have hzn : z ^ (-(1 / ν)) = (ν * k / L)⁻¹ := by
        rw [Real.rpow_neg hz0.le, hzr]
      rw [hzn] at h1
      have := (inv_mul_lt_iff₀ hbase).1 h1
      calc Real.log (seriesSum c z) < ν * k / L * L := this
        _ = ν * k := by field_simp
    have hFpos : 0 < seriesSum c z :=
      lt_of_lt_of_le one_pos (one_le_seriesSum hc hc0 hz0.le (hF z hz0.le))
    have hterm := term_le_seriesSum hc hz0.le (hF z hz0.le) k
    -- `log c_k + k ν log(νk/L) < ν k`
    have hlogc : Real.log (c k) + k * (ν * Real.log (ν * k / L)) < ν * k := by
      have h2 := Real.log_le_log (by positivity) hterm
      rw [Real.log_mul hck.ne' (by positivity), Real.log_pow, hzdef,
        Real.log_rpow hbase] at h2
      linarith
    have hlogk := (SeriesType.log_factorial_bounds k hk1).2
    set w := (k ! : ℝ) ^ ν * c k with hw
    have hwpos : 0 < w := by positivity
    have hlogw : Real.log w = ν * Real.log (k ! : ℝ) + Real.log (c k) := by
      rw [hw, Real.log_mul (by positivity) hck.ne', Real.log_rpow hfact]
    have hsplit : Real.log (ν * k / L) = Real.log k - Real.log (L / ν) := by
      rw [show ν * (k : ℝ) / L = k / (L / ν) by field_simp,
        Real.log_div hk0.ne' (by positivity)]
    have hmain : Real.log w * (1 / k) ≤ ν * ((Real.log k + 1) / k) + Real.log (L / ν) * ν := by
      rw [hlogw]
      rw [hsplit] at hlogc
      have hkk : (k : ℝ) * (1 / k) = 1 := by field_simp
      have e1 : (ν * Real.log (k ! : ℝ) + Real.log (c k)) * (1 / k) ≤
          (ν * ((k : ℝ) * Real.log k - k + 1 + Real.log k) +
            (ν * k - k * (ν * (Real.log k - Real.log (L / ν))))) * (1 / k) := by
        gcongr
        nlinarith [hlogk, hν]
      refine e1.trans (le_of_eq ?_)
      field_simp
      ring
    rw [Real.rpow_def_of_pos hwpos, hg]
    simp only
    rw [Real.rpow_def_of_pos (by positivity : 0 < L / ν), ← Real.exp_add]
    exact Real.exp_le_exp.2 hmain
  calc coeffType ν c ≤ limsup (fun k => ENNReal.ofReal (g k)) atTop :=
        limsup_le_limsup hbound (by isBoundedDefault) (by isBoundedDefault)
    _ = ENNReal.ofReal ((L / ν) ^ ν) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp hgt).limsup_eq

/-- Auxiliary (Lean route): for `κ > 0`, `z^{-κ}(A + B log z) → 0` as `z → ∞`
(used for the TeX's "the polynomial contributes zero to the normalized
logarithmic growth", main TeX lines 7259-7260, and for the polynomial prefactor of
`E:full-upper-bound`). -/
theorem tendsto_rpow_neg_mul_affine_log {κ : ℝ} (hκ : 0 < κ) (A B : ℝ) :
    Tendsto (fun z : ℝ => z ^ (-κ) * (A + B * Real.log z)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => z ^ (-κ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hκ
  have h2 : Tendsto (fun z : ℝ => Real.log z / z ^ κ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hκ).tendsto_div_nhds_zero
  have h3 := (h1.mul_const A).add (h2.const_mul B)
  simp only [zero_mul, mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  rw [Real.rpow_neg hz.le]
  field_simp

/-- **Second half of `L:positive-series-type`** (main TeX lines 7251-7262): if
`K < A` (with `A > 0`), then `τ ≤ ν A^{1/ν}`. Needs `ν ≥ 1` (for the
`ℓ^ν` bound `SeriesType.seriesNu_summable_le`). Route as in the TeX: all
large coefficients obey `c_k ≤ A^k/(k!)^ν`, so
`F(z) ≤ P(z) + exp(ν (Az)^{1/ν})` with a polynomial `P` with nonnegative
coefficients; here `P(z) ≤ D z^N` for `z ≥ 1`. -/
theorem seriesType_le_of_coeffType_lt {ν : ℝ} (hν : 1 ≤ ν) {c : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hc0 : c 0 = 1)
    (hF : ∀ z, 0 ≤ z → Summable (fun k => c k * z ^ k)) (A : ℝ) (hA : 0 < A)
    (hK : coeffType ν c < ENNReal.ofReal A) :
    seriesType ν c ≤ ((ν * A ^ (1 / ν) : ℝ) : EReal) := by
  have hν0 : 0 < ν := by linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (((k ! : ℝ) ^ ν * c k) ^ ((1 : ℝ) / k)) < ENNReal.ofReal A :=
    eventually_lt_of_limsup_lt hK (by isBoundedDefault)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set N := max N0 1 with hNdef
  -- coefficient bound for `k ≥ N`
  have hcoef : ∀ k, N ≤ k → c k ≤ A ^ k / (k ! : ℝ) ^ ν := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
    have hfact : (0 : ℝ) < (k ! : ℝ) ^ ν := by positivity
    have h := (ENNReal.ofReal_lt_ofReal_iff hA).1 (hN0 k (le_trans (le_max_left _ _) hk))
    have hwnn : 0 ≤ (k ! : ℝ) ^ ν * c k := mul_nonneg hfact.le (hc k)
    have hw : (k ! : ℝ) ^ ν * c k ≤ A ^ k := by
      have hkne : k ≠ 0 := by omega
      have e : (((k ! : ℝ) ^ ν * c k) ^ ((1 : ℝ) / k)) ^ k = (k ! : ℝ) ^ ν * c k := by
        rw [one_div]; exact Real.rpow_inv_natCast_pow hwnn hkne
      rw [← e]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hwnn _) h.le k
    rw [le_div_iff₀ hfact, mul_comm]; exact hw
  set D := ∑ k ∈ Finset.range N, c k with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun k _ => hc k
  -- the bound on `log F(z)` for `z ≥ 1`
  have hlog : ∀ z : ℝ, 1 ≤ z →
      Real.log (seriesSum c z) ≤
        Real.log (D + 1) + N * Real.log z + ν * (A ^ (1 / ν) * z ^ (1 / ν)) := by
    intro z hz
    have hz0 : 0 ≤ z := by linarith
    have hAz : 0 ≤ A * z := by positivity
    obtain ⟨hSs, hSle⟩ := SeriesType.seriesNu_summable_le hν hAz
    set P : ℕ → ℝ := fun k => if k < N then c k * z ^ k else 0 with hP
    have hPs : Summable P := summable_of_ne_finset_zero (s := Finset.range N)
      (fun k hk => by simp only [Finset.mem_range] at hk; simp [hP, hk])
    have hPsum : ∑' k, P k = ∑ k ∈ Finset.range N, c k * z ^ k := by
      rw [tsum_eq_sum (s := Finset.range N)
        (fun k hk => by simp only [Finset.mem_range] at hk; simp [hP, hk])]
      exact Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_range] at hk; simp [hP, hk]
    have hterm : ∀ k, c k * z ^ k ≤ P k + (A * z) ^ k / (k ! : ℝ) ^ ν := by
      intro k
      by_cases hk : k < N
      · simp only [hP, hk, ite_true]
        have : 0 ≤ (A * z) ^ k / (k ! : ℝ) ^ ν := by positivity
        linarith
      · simp only [hP, hk, ite_false, zero_add]
        have := hcoef k (not_lt.1 hk)
        calc c k * z ^ k ≤ A ^ k / (k ! : ℝ) ^ ν * z ^ k := by gcongr
          _ = (A * z) ^ k / (k ! : ℝ) ^ ν := by rw [mul_pow]; ring
    have hFle : seriesSum c z ≤ D * z ^ N + Real.exp (ν * (A * z) ^ (1 / ν)) := by
      calc seriesSum c z ≤ ∑' k, (P k + (A * z) ^ k / (k ! : ℝ) ^ ν) :=
            Summable.tsum_le_tsum hterm (hF z hz0) (hPs.add hSs)
        _ = ∑ k ∈ Finset.range N, c k * z ^ k + ∑' k, (A * z) ^ k / (k ! : ℝ) ^ ν := by
            rw [hPs.tsum_add hSs, hPsum]
        _ ≤ D * z ^ N + Real.exp (ν * (A * z) ^ (1 / ν)) := by
            gcongr
            rw [hD, Finset.sum_mul]
            refine Finset.sum_le_sum fun k hk => ?_
            simp only [Finset.mem_range] at hk
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz hk.le) (hc k)
    set E := Real.exp (ν * (A * z) ^ (1 / ν)) with hE
    have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
    have hzN : 1 ≤ z ^ N := one_le_pow₀ hz
    have hF1 : 1 ≤ seriesSum c z := one_le_seriesSum hc hc0 hz0 (hF z hz0)
    have hprod : seriesSum c z ≤ ((D + 1) * z ^ N) * E := by
      have : D * z ^ N + E ≤ ((D + 1) * z ^ N) * E := by
        nlinarith [mul_nonneg hD0 (by linarith : (0:ℝ) ≤ z ^ N)]
      linarith
    have := Real.log_le_log (by linarith) hprod
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, hE, Real.log_exp,
      Real.mul_rpow hA.le hz0] at this
    linarith
  -- conclude with the auxiliary limsup bound
  have hlim := tendsto_rpow_neg_mul_affine_log (by positivity : (0:ℝ) < 1 / ν)
    (Real.log (D + 1)) N
  refine limsup_le_of_eventually_le_add _ _ fun ε hε => ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (hlim.eventually (gt_mem_nhds hε))] with z hz hsmall
  have hz0 : 0 < z := by linarith
  have hzpos : 0 < z ^ (-(1 / ν)) := Real.rpow_pos_of_pos hz0 _
  have hcancel : z ^ (-(1 / ν)) * z ^ (1 / ν) = 1 := by
    rw [← Real.rpow_add hz0, neg_add_cancel, Real.rpow_zero]
  have h1 := mul_le_mul_of_nonneg_left (hlog z hz) hzpos.le
  have e : z ^ (-(1 / ν)) * (Real.log (D + 1) + N * Real.log z +
      ν * (A ^ (1 / ν) * z ^ (1 / ν))) =
      z ^ (-(1 / ν)) * (Real.log (D + 1) + N * Real.log z) +
        ν * A ^ (1 / ν) * (z ^ (-(1 / ν)) * z ^ (1 / ν)) := by ring
  rw [e, hcancel, mul_one] at h1
  linarith

/-! ### `L:positive-series-type`: the statement -/

/-- **`L:positive-series-type`** (Type of a positive coefficient series; main
TeX lines 7222-7234, proof 7236-7263), with the manuscript's hypotheses:
`ν ≥ 1`, `c_k ≥ 0`, `c_0 = 1`, and `F(z) = ∑ c_k z^k < ∞` for every `z ≥ 0`
(made explicit as summability, since a Lean `tsum` of a non-summable family is
`0`). If `τ < ∞` then `K < ∞` and `τ = ν K^{1/ν}`; conversely finite `K`
implies finite `τ` and the same equality. `τ` is an extended real
(`seriesType`), `K` is in `ℝ≥0∞` (`coeffType`), and the equality is stated
with `K.toReal`, which is `K` itself because `K < ∞` is part of each
conclusion. -/
theorem positive_series_type_paper {ν : ℝ} (hν : 1 ≤ ν) {c : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hc0 : c 0 = 1)
    (hF : ∀ z, 0 ≤ z → Summable (fun k => c k * z ^ k)) :
    (seriesType ν c < ⊤ → coeffType ν c < ⊤ ∧
        seriesType ν c = ((ν * (coeffType ν c).toReal ^ (1 / ν) : ℝ) : EReal)) ∧
      (coeffType ν c < ⊤ → seriesType ν c < ⊤ ∧
        seriesType ν c = ((ν * (coeffType ν c).toReal ^ (1 / ν) : ℝ) : EReal)) := by
  have hν0 : 0 < ν := by linarith
  have hτ0 := seriesType_nonneg (ν := ν) hc hc0 hF
  -- key 1: finite `τ` bounds `K`
  have key1 : ∀ t : ℝ, seriesType ν c = (t : EReal) →
      coeffType ν c < ⊤ ∧ ν * (coeffType ν c).toReal ^ (1 / ν) ≤ t := by
    intro t ht
    have ht0 : 0 ≤ t := by rw [ht] at hτ0; exact EReal.coe_nonneg.1 hτ0
    have hK : coeffType ν c ≤ ENNReal.ofReal ((t / ν) ^ ν) := by
      have hcont : Tendsto (fun L : ℝ => ENNReal.ofReal ((L / ν) ^ ν)) (𝓝[>] t)
          (𝓝 (ENNReal.ofReal ((t / ν) ^ ν))) := by
        have : Continuous (fun L : ℝ => ENNReal.ofReal ((L / ν) ^ ν)) :=
          ENNReal.continuous_ofReal.comp
            ((continuous_id.div_const ν).rpow_const fun _ => Or.inr hν0.le)
        exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto hcont ?_
      filter_upwards [self_mem_nhdsWithin] with L hL
      exact coeffType_le_of_seriesType_lt hν0 hc hc0 hF L
        (by rw [ht]; exact EReal.coe_lt_coe_iff.2 hL)
    have hKfin : coeffType ν c < ⊤ := lt_of_le_of_lt hK ENNReal.ofReal_lt_top
    refine ⟨hKfin, ?_⟩
    have hKr : (coeffType ν c).toReal ≤ (t / ν) ^ ν :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hK
    have h2 : (coeffType ν c).toReal ^ (1 / ν) ≤ t / ν := by
      calc (coeffType ν c).toReal ^ (1 / ν) ≤ ((t / ν) ^ ν) ^ (1 / ν) :=
            Real.rpow_le_rpow ENNReal.toReal_nonneg hKr (by positivity)
        _ = t / ν := by rw [one_div, Real.rpow_rpow_inv (by positivity) hν0.ne']
    calc ν * (coeffType ν c).toReal ^ (1 / ν) ≤ ν * (t / ν) := by gcongr
      _ = t := by field_simp
  -- key 2: finite `K` bounds `τ`
  have key2 : coeffType ν c < ⊤ →
      seriesType ν c ≤ ((ν * (coeffType ν c).toReal ^ (1 / ν) : ℝ) : EReal) := by
    intro hKfin
    set kk := (coeffType ν c).toReal with hkk
    have hkk0 : 0 ≤ kk := ENNReal.toReal_nonneg
    have hKeq : coeffType ν c = ENNReal.ofReal kk := (ENNReal.ofReal_toReal hKfin.ne).symm
    have hcont : Tendsto (fun A : ℝ => ((ν * A ^ (1 / ν) : ℝ) : EReal)) (𝓝[>] kk)
        (𝓝 ((ν * kk ^ (1 / ν) : ℝ) : EReal)) := by
      have : Continuous (fun A : ℝ => ((ν * A ^ (1 / ν) : ℝ) : EReal)) :=
        continuous_coe_real_ereal.comp
          (continuous_const.mul (Real.continuous_rpow_const (by positivity)))
      exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with A hA
    have hA0 : 0 < A := lt_of_le_of_lt hkk0 hA
    exact seriesType_le_of_coeffType_lt hν hc hc0 hF A hA0
      (by rw [hKeq]; exact (ENNReal.ofReal_lt_ofReal_iff hA0).2 hA)
  -- assemble
  have fromτ : seriesType ν c < ⊤ → coeffType ν c < ⊤ ∧
      seriesType ν c = ((ν * (coeffType ν c).toReal ^ (1 / ν) : ℝ) : EReal) := by
    intro hτ
    have hne_bot : seriesType ν c ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hτ0
    set t := (seriesType ν c).toReal with htdef
    have ht : seriesType ν c = (t : EReal) := (EReal.coe_toReal hτ.ne hne_bot).symm
    obtain ⟨hKfin, hle⟩ := key1 t ht
    refine ⟨hKfin, le_antisymm (key2 hKfin) ?_⟩
    rw [ht]; exact EReal.coe_le_coe_iff.2 hle
  refine ⟨fromτ, fun hKfin => ?_⟩
  have hτ : seriesType ν c < ⊤ := lt_of_le_of_lt (key2 hKfin) (EReal.coe_lt_top _)
  exact ⟨hτ, (fromτ hτ).2⟩

/-! ### Non-vacuity: the model family `c_k = A^k/(k!)^ν` -/

/-- Auxiliary (non-vacuity check, not a TeX step): the coefficient type of
`c_k = A^k/(k!)^ν` is `A` (`A ≥ 0`, any real `ν`). -/
theorem coeffType_exp_family (ν : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    coeffType ν (fun k => A ^ k / (k ! : ℝ) ^ ν) = ENNReal.ofReal A := by
  unfold coeffType
  have hev : (fun k : ℕ => ENNReal.ofReal
      (((k ! : ℝ) ^ ν * (A ^ k / (k ! : ℝ) ^ ν)) ^ ((1 : ℝ) / k))) =ᶠ[atTop]
      fun _ => ENNReal.ofReal A := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hf : (0 : ℝ) < (k ! : ℝ) ^ ν := by positivity
    have hkne : k ≠ 0 := by omega
    rw [mul_div_cancel₀ _ hf.ne', one_div, Real.pow_rpow_inv_natCast hA hkne]
  rw [limsup_congr hev, limsup_const]

/-- Auxiliary (non-vacuity check, not a TeX step): for `ν ≥ 1` and `A ≥ 0`,
the family `c_k = A^k/(k!)^ν` satisfies the hypotheses of
`L:positive-series-type`, and its type is `τ = ν A^{1/ν}` (by
`positive_series_type_paper` and `coeffType_exp_family`). -/
theorem seriesType_exp_family {ν A : ℝ} (hν : 1 ≤ ν) (hA : 0 ≤ A) :
    (∀ k, 0 ≤ A ^ k / (k ! : ℝ) ^ ν) ∧ A ^ 0 / ((0 ! : ℕ) : ℝ) ^ ν = 1 ∧
      (∀ z : ℝ, 0 ≤ z → Summable (fun k => A ^ k / (k ! : ℝ) ^ ν * z ^ k)) ∧
      seriesType ν (fun k => A ^ k / (k ! : ℝ) ^ ν) = ((ν * A ^ (1 / ν) : ℝ) : EReal) := by
  have hc : ∀ k, 0 ≤ A ^ k / (k ! : ℝ) ^ ν := fun k => by positivity
  have hc0 : A ^ 0 / ((0 ! : ℕ) : ℝ) ^ ν = 1 := by simp
  have hF : ∀ z : ℝ, 0 ≤ z → Summable (fun k => A ^ k / (k ! : ℝ) ^ ν * z ^ k) := by
    intro z hz
    refine (SeriesType.seriesNu_summable_le hν (mul_nonneg hA hz)).1.congr fun k => ?_
    rw [mul_pow]; ring
  refine ⟨hc, hc0, hF, ?_⟩
  have hK := coeffType_exp_family ν hA
  have h := (positive_series_type_paper hν hc hc0 hF).2
    (by rw [hK]; exact ENNReal.ofReal_lt_top)
  rw [h.2, hK, ENNReal.toReal_ofReal hA]

/-! ### Growth rates and their identification with the series type -/

/-- The normalized upper time growth rate
`limsup_{T → ∞} T^{-κ} log m(T)` of `E:moment-growth-types` (main TeX
lines 7505-7514), as an extended real number. -/
def growthUpper (κ : ℝ) (m : ℝ → ℝ) : EReal :=
  limsup (fun T : ℝ => ((T ^ (-κ) * Real.log (m T) : ℝ) : EReal)) atTop

/-- The normalized lower time growth rate
`liminf_{T → ∞} T^{-κ} log m(T)` of `E:moment-growth-types` (main TeX
lines 7505-7514), as an extended real number. -/
def growthLower (κ : ℝ) (m : ℝ → ℝ) : EReal :=
  liminf (fun T : ℝ => ((T ^ (-κ) * Real.log (m T) : ℝ) : EReal)) atTop

/-- Auxiliary (Lean route): the substitution `T = z^{1/β}` maps `atTop` onto
`atTop` (`β > 0`). -/
theorem map_rpow_inv_atTop {β : ℝ} (hβ : 0 < β) :
    map (fun z : ℝ => z ^ (1 / β)) atTop = atTop := by
  refine le_antisymm (tendsto_rpow_atTop (by positivity)) ?_
  have hh : Tendsto (fun T : ℝ => T ^ β) atTop atTop := tendsto_rpow_atTop hβ
  have hid : (fun z : ℝ => z ^ (1 / β)) ∘ (fun T : ℝ => T ^ β) =ᶠ[atTop] id := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simp only [Function.comp, id]
    rw [one_div, Real.rpow_rpow_inv hT hβ.ne']
  calc atTop = map id atTop := map_id.symm
    _ = map ((fun z : ℝ => z ^ (1 / β)) ∘ (fun T : ℝ => T ^ β)) atTop := (map_congr hid).symm
    _ = map (fun z : ℝ => z ^ (1 / β)) (map (fun T : ℝ => T ^ β) atTop) := map_map.symm
    _ ≤ map (fun z : ℝ => z ^ (1 / β)) atTop := map_mono hh

/-- **The identification of the growth rate with the series type** (main TeX
lines 7539-7543, in the proof of `P:moment-growth-logconvex`): if
`m(t) = F(t^β)` for every `t > 0`, then the substitution `z = T^β` gives
`limsup_T T^{-β/ν} log m(T) = limsup_z z^{-1/ν} log F(z)`, i.e. the growth
rate at `κ = β/ν` equals the type `τ` of `L:positive-series-type`. Proved
here, not supplied. `β, ν > 0`. -/
theorem growthUpper_eq_seriesType {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) {m : ℝ → ℝ}
    {c : ℕ → ℝ} (hm : ∀ t : ℝ, 0 < t → m t = seriesSum c (t ^ β)) :
    growthUpper (β / ν) m = seriesType ν c := by
  unfold growthUpper seriesType
  set u : ℝ → EReal := fun T => ((T ^ (-(β / ν)) * Real.log (m T) : ℝ) : EReal) with hu
  calc limsup u atTop = limsup u (map (fun z : ℝ => z ^ (1 / β)) atTop) := by
        rw [map_rpow_inv_atTop hβ]
    _ = limsup (u ∘ fun z : ℝ => z ^ (1 / β)) atTop := (limsup_comp _ _ _).symm
    _ = _ := by
        refine limsup_congr ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        simp only [hu, Function.comp]
        have h1 : (z ^ (1 / β)) ^ (-(β / ν)) = z ^ (-(1 / ν)) := by
          rw [← Real.rpow_mul hz.le]; congr 1; field_simp
        have h2 : (z ^ (1 / β)) ^ β = z := by
          rw [one_div, Real.rpow_inv_rpow hz.le hβ.ne']
        rw [h1, hm _ (Real.rpow_pos_of_pos hz _), h2]

/-! ### Coefficient interpolation and the upper growth type -/

/-- **The coefficient-type interpolation** (main TeX lines 7550-7556, in the
proof of `P:moment-growth-logconvex`): if `c_k ≤ c1_k^{1-θ} c2_k^θ` for every
`k` with `0 < θ < 1`, and both endpoint types are finite, then
`K ≤ K1^{1-θ} K2^θ`. As in the TeX, the endpoint root sequences are eventually
bounded by `K_i + η` and `η ↓ 0` at the end, so zero or oscillating
coefficients are allowed. -/
theorem coeffType_interp {ν θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {c c1 c2 : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hc1 : ∀ k, 0 ≤ c1 k) (hc2 : ∀ k, 0 ≤ c2 k)
    (hhol : ∀ k, c k ≤ c1 k ^ (1 - θ) * c2 k ^ θ)
    (hK1 : coeffType ν c1 < ⊤) (hK2 : coeffType ν c2 < ⊤) :
    coeffType ν c ≤
      ENNReal.ofReal ((coeffType ν c1).toReal ^ (1 - θ) * (coeffType ν c2).toReal ^ θ) := by
  set K1 := (coeffType ν c1).toReal
  set K2 := (coeffType ν c2).toReal
  have hK10 : 0 ≤ K1 := ENNReal.toReal_nonneg
  have hK20 : 0 ≤ K2 := ENNReal.toReal_nonneg
  set r : (ℕ → ℝ) → ℕ → ℝ := fun c k => ((k ! : ℝ) ^ ν * c k) ^ ((1 : ℝ) / k) with hr
  -- pointwise interpolation of the root sequences
  have hpt : ∀ k, r c k ≤ r c1 k ^ (1 - θ) * r c2 k ^ θ := by
    intro k
    have hf : (0 : ℝ) < (k ! : ℝ) ^ ν := by positivity
    have hsplit : (k ! : ℝ) ^ ν = ((k ! : ℝ) ^ ν) ^ (1 - θ) * ((k ! : ℝ) ^ ν) ^ θ := by
      rw [← Real.rpow_add hf, sub_add_cancel, Real.rpow_one]
    have h1 : (k ! : ℝ) ^ ν * c k ≤
        ((k ! : ℝ) ^ ν * c1 k) ^ (1 - θ) * ((k ! : ℝ) ^ ν * c2 k) ^ θ := by
      rw [Real.mul_rpow hf.le (hc1 k), Real.mul_rpow hf.le (hc2 k)]
      calc (k ! : ℝ) ^ ν * c k ≤ (k ! : ℝ) ^ ν * (c1 k ^ (1 - θ) * c2 k ^ θ) := by
            gcongr; exact hhol k
        _ = ((k ! : ℝ) ^ ν) ^ (1 - θ) * ((k ! : ℝ) ^ ν) ^ θ *
              (c1 k ^ (1 - θ) * c2 k ^ θ) := by rw [← hsplit]
        _ = _ := by ring
    have hnn1 : 0 ≤ (k ! : ℝ) ^ ν * c1 k := mul_nonneg hf.le (hc1 k)
    have hnn2 : 0 ≤ (k ! : ℝ) ^ ν * c2 k := mul_nonneg hf.le (hc2 k)
    simp only [hr]
    calc ((k ! : ℝ) ^ ν * c k) ^ ((1 : ℝ) / k)
        ≤ (((k ! : ℝ) ^ ν * c1 k) ^ (1 - θ) * ((k ! : ℝ) ^ ν * c2 k) ^ θ) ^ ((1 : ℝ) / k) :=
          Real.rpow_le_rpow (mul_nonneg hf.le (hc k)) h1 (by positivity)
      _ = _ := by
          rw [Real.mul_rpow (Real.rpow_nonneg hnn1 _) (Real.rpow_nonneg hnn2 _),
            ← Real.rpow_mul hnn1, ← Real.rpow_mul hnn2, ← Real.rpow_mul hnn1,
            ← Real.rpow_mul hnn2, mul_comm (1 - θ), mul_comm θ]
  -- eventual bounds by `K_i + η`
  have hev : ∀ (c' : ℕ → ℝ), coeffType ν c' < ⊤ → ∀ η : ℝ, 0 < η →
      ∀ᶠ k in atTop, r c' k < (coeffType ν c').toReal + η := by
    intro c' hK η hη
    have hlt : coeffType ν c' < ENNReal.ofReal ((coeffType ν c').toReal + η) := by
      rw [← ENNReal.ofReal_toReal hK.ne] at ⊢
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    filter_upwards [eventually_lt_of_limsup_lt hlt (by isBoundedDefault)] with k hk
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hk
  have hbd : ∀ η : ℝ, 0 < η →
      coeffType ν c ≤ ENNReal.ofReal ((K1 + η) ^ (1 - θ) * (K2 + η) ^ θ) := by
    intro η hη
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hev c1 hK1 η hη, hev c2 hK2 η hη] with k hk1 hk2
    refine ENNReal.ofReal_le_ofReal ((hpt k).trans ?_)
    have h1nn : 0 ≤ r c1 k := Real.rpow_nonneg (mul_nonneg (by positivity) (hc1 k)) _
    have h2nn : 0 ≤ r c2 k := Real.rpow_nonneg (mul_nonneg (by positivity) (hc2 k)) _
    gcongr
  have hcont : Tendsto (fun η : ℝ => ENNReal.ofReal ((K1 + η) ^ (1 - θ) * (K2 + η) ^ θ))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (K1 ^ (1 - θ) * K2 ^ θ))) := by
    have hc' : Continuous (fun η : ℝ => ENNReal.ofReal ((K1 + η) ^ (1 - θ) * (K2 + η) ^ θ)) :=
      ENNReal.continuous_ofReal.comp
        (((continuous_const.add continuous_id).rpow_const fun _ => Or.inr (by linarith)).mul
          ((continuous_const.add continuous_id).rpow_const fun _ => Or.inr hθ0.le))
    have := hc'.continuousAt (x := 0)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun η hη => hbd η hη)

/-- Auxiliary (Lean route): `ν (x^{1-θ} y^θ)^{1/ν} = (ν x^{1/ν})^{1-θ}(ν y^{1/ν})^θ`
for `x, y ≥ 0` and `ν > 0` (the TeX's "taking the `1/ν` power and multiplying
by `ν`", main TeX lines 7558-7559). -/
theorem nu_rpow_interp {ν θ x y : ℝ} (hν : 0 < ν) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ν * (x ^ (1 - θ) * y ^ θ) ^ (1 / ν) =
      (ν * x ^ (1 / ν)) ^ (1 - θ) * (ν * y ^ (1 / ν)) ^ θ := by
  have hνν : ν ^ (1 - θ) * ν ^ θ = ν := by
    rw [← Real.rpow_add hν, sub_add_cancel, Real.rpow_one]
  rw [Real.mul_rpow (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _),
    Real.mul_rpow hν.le (Real.rpow_nonneg hx _), Real.mul_rpow hν.le (Real.rpow_nonneg hy _),
    ← Real.rpow_mul hx, ← Real.rpow_mul hy, ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_comm (1 / ν) (1 - θ), mul_comm (1 / ν) θ]
  calc ν * (x ^ ((1 - θ) * (1 / ν)) * y ^ (θ * (1 / ν)))
      = (ν ^ (1 - θ) * ν ^ θ) * (x ^ ((1 - θ) * (1 / ν)) * y ^ (θ * (1 / ν))) := by
        rw [hνν]
    _ = _ := by ring

/-- Auxiliary (Lean route): an extended real `x` with `0 < x < ⊤` is the
coercion of the positive real `x.toReal`. -/
theorem ereal_pos_fin {x : EReal} (h0 : 0 < x) (h1 : x < ⊤) :
    0 < x.toReal ∧ ((x.toReal : ℝ) : EReal) = x := by
  have hb : x ≠ ⊥ := ne_bot_of_gt h0
  have he := EReal.coe_toReal h1.ne hb
  refine ⟨?_, he⟩
  rw [← he] at h0
  exact EReal.coe_pos.1 h0

/-- Auxiliary (Lean route): summability of `∑ c_k z^k` at every `z ≥ 0` from
summability at `z = t^β` for every `t > 0` (every `z > 0` is `t^β`,
`t = z^{1/β}`; at `z = 0` the series is finite). -/
theorem summable_of_rpow {β : ℝ} (hβ : 0 < β) {c : ℕ → ℝ}
    (hs : ∀ t : ℝ, 0 < t → Summable (fun k => c k * (t ^ β) ^ k)) :
    ∀ z : ℝ, 0 ≤ z → Summable (fun k => c k * z ^ k) := by
  intro z hz
  rcases hz.eq_or_lt with h0 | hpos
  · subst h0
    exact summable_of_ne_finset_zero (s := {0}) fun k hk => by
      simp only [Finset.mem_singleton] at hk; simp [zero_pow hk]
  · have := hs (z ^ (1 / β)) (Real.rpow_pos_of_pos hpos _)
    rwa [one_div, Real.rpow_inv_rpow hpos.le hβ.ne'] at this

/-- **The upper growth rate as a coefficient type** (main TeX lines 7539-7549,
in the proof of `P:moment-growth-logconvex`): if `m(t) = ∑ c_k (t^β)^k` with
`c_k ≥ 0`, `c_0 = 1`, summable for `t > 0`, and the growth rate at
`κ = β/ν` is finite, then it equals `ν K^{1/ν}` with `K` the (finite)
coefficient type, by `growthUpper_eq_seriesType` and
`L:positive-series-type`. `ν ≥ 1`, `β > 0`. -/
theorem growthUpper_eq_coeffType {ν β : ℝ} (hν : 1 ≤ ν) (hβ : 0 < β) {m : ℝ → ℝ}
    {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (hc0 : c 0 = 1)
    (hser : ∀ t : ℝ, 0 < t → Summable (fun k => c k * (t ^ β) ^ k) ∧
      m t = ∑' k, c k * (t ^ β) ^ k)
    (hfin : growthUpper (β / ν) m < ⊤) :
    coeffType ν c < ⊤ ∧
      growthUpper (β / ν) m = ((ν * (coeffType ν c).toReal ^ (1 / ν) : ℝ) : EReal) := by
  have hν0 : 0 < ν := by linarith
  have hid := growthUpper_eq_seriesType hβ hν0 (m := m) (c := c)
    (fun t ht => (hser t ht).2)
  have hF := summable_of_rpow hβ (fun t ht => (hser t ht).1)
  rw [hid] at hfin ⊢
  exact (positive_series_type_paper hν hc hc0 hF).1 hfin

/-- **Core of `P:moment-growth-logconvex`** (main TeX lines 7516-7572), for a
single family of moments `m a` with coefficients `c a`, an exponent map `β`
and `κ(a) = β(a)/ν`, over the range `0 ≤ a < amax`. Inputs (each a hypothesis
of this general statement): the positive coefficient series with `c_0 = 1`
(`E:full-moment-positive-series`), the coefficient interpolation
(`E:full-moment-coefficient-holder`), and positivity and finiteness of the
upper growth rate. Conclusions, for the real rate
`λ(a) = (growthUpper (β a / ν) (m a)).toReal` (which is the rate itself by
finiteness): `E:moment-growth-logconvex`, convexity of `log λ` on `[0, amax)`
and continuity of `λ` and `log λ` on `(0, amax)`. Continuity uses
`ConvexOn.continuousOn_interior` instead of the TeX's secant-slope argument
(main TeX lines 7561-7570), same statement. -/
theorem growth_logconvex_core {ν amax : ℝ} (hν : 1 ≤ ν) (β : ℝ → ℝ)
    (hβ : ∀ a ∈ Ico 0 amax, 0 < β a) (m : ℝ → ℝ → ℝ) (c : ℝ → ℕ → ℝ)
    (hser : ∀ a ∈ Ico 0 amax, (∀ k, 0 ≤ c a k) ∧ c a 0 = 1 ∧ ∀ t : ℝ, 0 < t →
      Summable (fun k => c a k * (t ^ β a) ^ k) ∧ m a t = ∑' k, c a k * (t ^ β a) ^ k)
    (hhol : ∀ a1 a a2 : ℝ, 0 ≤ a1 → a1 < a → a < a2 → a2 < amax → ∀ k,
      c a k ≤ c a1 k ^ (1 - (a - a1) / (a2 - a1)) * c a2 k ^ ((a - a1) / (a2 - a1)))
    (hpos : ∀ a ∈ Ico 0 amax, 0 < growthUpper (β a / ν) (m a))
    (hfin : ∀ a ∈ Ico 0 amax, growthUpper (β a / ν) (m a) < ⊤) :
    (∀ a1 a a2 : ℝ, 0 ≤ a1 → a1 < a → a < a2 → a2 < amax →
      (growthUpper (β a / ν) (m a)).toReal ≤
        (growthUpper (β a1 / ν) (m a1)).toReal ^ (1 - (a - a1) / (a2 - a1)) *
          (growthUpper (β a2 / ν) (m a2)).toReal ^ ((a - a1) / (a2 - a1))) ∧
      ConvexOn ℝ (Ico 0 amax) (fun a => Real.log (growthUpper (β a / ν) (m a)).toReal) ∧
      ContinuousOn (fun a => (growthUpper (β a / ν) (m a)).toReal) (Ioo 0 amax) ∧
      ContinuousOn (fun a => Real.log (growthUpper (β a / ν) (m a)).toReal) (Ioo 0 amax) := by
  have hν0 : 0 < ν := by linarith
  set lam : ℝ → ℝ := fun a => (growthUpper (β a / ν) (m a)).toReal with hlam
  -- the rate as a coefficient type
  have hrep : ∀ a ∈ Ico 0 amax, coeffType ν (c a) < ⊤ ∧
      lam a = ν * (coeffType ν (c a)).toReal ^ (1 / ν) := by
    intro a ha
    obtain ⟨hc, hc0, hs⟩ := hser a ha
    obtain ⟨hK, he⟩ := growthUpper_eq_coeffType hν (hβ a ha) hc hc0 hs (hfin a ha)
    refine ⟨hK, ?_⟩
    simp only [hlam, he, EReal.toReal_coe]
  have hlampos : ∀ a ∈ Ico 0 amax, 0 < lam a := fun a ha =>
    (ereal_pos_fin (hpos a ha) (hfin a ha)).1
  -- E:moment-growth-logconvex
  have hineq : ∀ a1 a a2 : ℝ, 0 ≤ a1 → a1 < a → a < a2 → a2 < amax →
      lam a ≤ lam a1 ^ (1 - (a - a1) / (a2 - a1)) * lam a2 ^ ((a - a1) / (a2 - a1)) := by
    intro a1 a a2 h0 h1 h2 h3
    have ha1 : a1 ∈ Ico 0 amax := ⟨h0, by linarith⟩
    have ha : a ∈ Ico 0 amax := ⟨by linarith, by linarith⟩
    have ha2 : a2 ∈ Ico 0 amax := ⟨by linarith, h3⟩
    set θ := (a - a1) / (a2 - a1) with hθ
    have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
    have hθ1 : θ < 1 := (div_lt_one (by linarith)).2 (by linarith)
    obtain ⟨hK1, he1⟩ := hrep a1 ha1
    obtain ⟨hK, he⟩ := hrep a ha
    obtain ⟨hK2, he2⟩ := hrep a2 ha2
    have hint := coeffType_interp hθ0 hθ1 (hser a ha).1 (hser a1 ha1).1 (hser a2 ha2).1
      (hhol a1 a a2 h0 h1 h2 h3) hK1 hK2
    have hKr : (coeffType ν (c a)).toReal ≤
        (coeffType ν (c a1)).toReal ^ (1 - θ) * (coeffType ν (c a2)).toReal ^ θ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hint
    rw [he, he1, he2, ← nu_rpow_interp hν0 ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    gcongr
  refine ⟨hineq, ?_⟩
  · -- convexity of `log λ` on `[0, amax)`
    have hconv : ConvexOn ℝ (Ico 0 amax) (fun a => Real.log (lam a)) := by
      refine convexOn_iff_forall_pos.2 ⟨convex_Ico 0 amax, ?_⟩
      intro x hx y hy s t hs ht hst
      simp only [smul_eq_mul]
      have key : ∀ x y : ℝ, x ∈ Ico 0 amax → y ∈ Ico 0 amax → x < y →
          ∀ s t : ℝ, 0 < s → 0 < t → s + t = 1 →
          Real.log (lam (s * x + t * y)) ≤ s * Real.log (lam x) + t * Real.log (lam y) := by
        intro x y hx hy hxy s t hs ht hst
        have hs' : s = 1 - t := by linarith
        have hm1 : x < s * x + t * y := by
          rw [hs']; nlinarith [mul_pos ht (sub_pos.2 hxy)]
        have hm2 : s * x + t * y < y := by
          rw [hs']; nlinarith [mul_pos hs (sub_pos.2 hxy)]
        have h := hineq x (s * x + t * y) y hx.1 hm1 hm2 hy.2
        have hθe : (s * x + t * y - x) / (y - x) = t := by
          rw [div_eq_iff (by linarith), hs']; ring
        rw [hθe, show 1 - t = s by linarith] at h
        have hpx := hlampos x hx
        have hpy := hlampos y hy
        have hpm := hlampos (s * x + t * y) ⟨by nlinarith [hx.1], by linarith [hy.2]⟩
        have := Real.log_le_log hpm h
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hpx,
          Real.log_rpow hpy] at this
        exact this
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · exact key x y hx hy hxy s t hs ht hst
      · subst hxy
        rw [show s * x + t * x = x by rw [← add_mul, hst, one_mul],
          ← add_mul, hst, one_mul]
      · have := key y x hy hx hxy t s ht hs (by linarith)
        rw [add_comm (t * y)] at this
        linarith
    refine ⟨hconv, ?_⟩
    -- continuity on the interior
    have hlogc : ContinuousOn (fun a => Real.log (lam a)) (Ioo 0 amax) := by
      have := hconv.continuousOn_interior
      rwa [interior_Ico] at this
    have hexp : ContinuousOn (fun a => Real.exp (Real.log (lam a))) (Ioo 0 amax) :=
      Real.continuous_exp.comp_continuousOn hlogc
    refine ⟨hexp.congr fun a ha => ?_, hlogc⟩
    exact (Real.exp_log (hlampos a ⟨ha.1.le, ha.2⟩)).symm

/-! ### Core of `C:static-moment-constant-continuity` -/

/-- Auxiliary (Lean route): an extended real between two real numbers is the
coercion of its `toReal`, which lies between them. -/
theorem ereal_toReal_between {x : EReal} {l u : ℝ} (hl : (l : EReal) ≤ x)
    (hu : x ≤ (u : EReal)) :
    l ≤ x.toReal ∧ x.toReal ≤ u ∧ ((x.toReal : ℝ) : EReal) = x := by
  have htop : x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top u) hu
  have hbot : x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot l) hl
  have he := EReal.coe_toReal htop hbot
  refine ⟨?_, ?_, he⟩
  · rw [← he] at hl; exact EReal.coe_le_coe_iff.1 hl
  · rw [← he] at hu; exact EReal.coe_le_coe_iff.1 hu

/-- Auxiliary (Lean route): if every `y < C` is eventually below `f`, then the
extended-real liminf of `f` is at least `C` (this is the real statement
`liminf f ≥ C`, with no boundedness side condition). -/
theorem le_liminf_of_forall_lt {α : Type*} {l : Filter α} (f : α → ℝ) (C : ℝ)
    (h : ∀ y < C, ∀ᶠ x in l, y ≤ f x) :
    (C : EReal) ≤ liminf (fun x => (f x : EReal)) l := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨y, hly, hyC⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hy : y < C := EReal.coe_lt_coe_iff.1 hyC
  have : (y : EReal) ≤ liminf (fun x => (f x : EReal)) l :=
    le_liminf_of_le (by isBoundedDefault)
      ((h y hy).mono fun x hx => EReal.coe_le_coe_iff.2 hx)
  exact absurd hly (not_lt.2 this)

/-- Auxiliary (Lean route): `C^{1-θ} x^θ = C (x/C)^θ` for `C > 0`, `x ≥ 0`. -/
theorem rpow_interp_eq {C x θ : ℝ} (hC : 0 < C) (hx : 0 ≤ x) :
    C ^ (1 - θ) * x ^ θ = C * (x / C) ^ θ := by
  rw [Real.div_rpow hx hC.le, Real.rpow_sub hC, Real.rpow_one]
  have : 0 < C ^ θ := Real.rpow_pos_of_pos hC θ
  field_simp

/-- **Core of `C:static-moment-constant-continuity`** (main TeX lines
7574-7606), for one family as in `growth_logconvex_core` and `amax > 0`.
Inputs besides those of the core proposition: the endpoint value
`Λ̄(0) = C > 0` and the lower bound `Λ̲(a) ≥ C` for `0 < a < amax`.
Conclusions: the envelope `E:static-constant-envelope`
`C ≤ Λ̲(a) ≤ Λ̄(a) ≤ C (Λ̄(b)/C)^{a/b}` for `0 < a < b < amax`, and
`E:static-constant-continuity` `Λ̲(a), Λ̄(a) → C` as `a ↓ 0`, both as extended
reals and for their `toReal` (which are the rates themselves by the envelope).
Route as in the TeX: the core interpolation with endpoints `0, b`, then a
squeeze. -/
theorem static_constant_core {ν amax : ℝ} (hν : 1 ≤ ν) (hamax : 0 < amax) (β : ℝ → ℝ)
    (hβ : ∀ a ∈ Ico 0 amax, 0 < β a) (m : ℝ → ℝ → ℝ) (c : ℝ → ℕ → ℝ)
    (hser : ∀ a ∈ Ico 0 amax, (∀ k, 0 ≤ c a k) ∧ c a 0 = 1 ∧ ∀ t : ℝ, 0 < t →
      Summable (fun k => c a k * (t ^ β a) ^ k) ∧ m a t = ∑' k, c a k * (t ^ β a) ^ k)
    (hhol : ∀ a1 a a2 : ℝ, 0 ≤ a1 → a1 < a → a < a2 → a2 < amax → ∀ k,
      c a k ≤ c a1 k ^ (1 - (a - a1) / (a2 - a1)) * c a2 k ^ ((a - a1) / (a2 - a1)))
    (hpos : ∀ a ∈ Ico 0 amax, 0 < growthUpper (β a / ν) (m a))
    (hfin : ∀ a ∈ Ico 0 amax, growthUpper (β a / ν) (m a) < ⊤)
    (C : ℝ) (hC : 0 < C) (h0 : growthUpper (β 0 / ν) (m 0) = (C : EReal))
    (hlow : ∀ a ∈ Ioo 0 amax, (C : EReal) ≤ growthLower (β a / ν) (m a)) :
    (∀ b ∈ Ioo 0 amax, ∀ a ∈ Ioo 0 b,
      (C : EReal) ≤ growthLower (β a / ν) (m a) ∧
        growthLower (β a / ν) (m a) ≤ growthUpper (β a / ν) (m a) ∧
        growthUpper (β a / ν) (m a) ≤
          ((C * ((growthUpper (β b / ν) (m b)).toReal / C) ^ (a / b) : ℝ) : EReal)) ∧
      Tendsto (fun a => growthLower (β a / ν) (m a)) (𝓝[>] 0) (𝓝 (C : EReal)) ∧
      Tendsto (fun a => growthUpper (β a / ν) (m a)) (𝓝[>] 0) (𝓝 (C : EReal)) ∧
      Tendsto (fun a => (growthLower (β a / ν) (m a)).toReal) (𝓝[>] 0) (𝓝 C) ∧
      Tendsto (fun a => (growthUpper (β a / ν) (m a)).toReal) (𝓝[>] 0) (𝓝 C) := by
  obtain ⟨hineq, -⟩ := growth_logconvex_core hν β hβ m c hser hhol hpos hfin
  have hlam0 : (growthUpper (β 0 / ν) (m 0)).toReal = C := by rw [h0]; rfl
  have henv : ∀ b ∈ Ioo 0 amax, ∀ a ∈ Ioo 0 b,
      (C : EReal) ≤ growthLower (β a / ν) (m a) ∧
        growthLower (β a / ν) (m a) ≤ growthUpper (β a / ν) (m a) ∧
        growthUpper (β a / ν) (m a) ≤
          ((C * ((growthUpper (β b / ν) (m b)).toReal / C) ^ (a / b) : ℝ) : EReal) := by
    intro b hb a ha
    have hamem : a ∈ Ioo 0 amax := ⟨ha.1, ha.2.trans hb.2⟩
    refine ⟨hlow a hamem, liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault), ?_⟩
    have hi := hineq 0 a b le_rfl ha.1 ha.2 hb.2
    simp only [sub_zero] at hi
    have hbI : b ∈ Ico 0 amax := ⟨hb.1.le, hb.2⟩
    have haI : a ∈ Ico 0 amax := ⟨ha.1.le, hamem.2⟩
    have hlb := (ereal_pos_fin (hpos b hbI) (hfin b hbI)).1
    rw [hlam0, rpow_interp_eq hC hlb.le] at hi
    rw [← (ereal_pos_fin (hpos a haI) (hfin a haI)).2]
    exact EReal.coe_le_coe_iff.2 hi
  refine ⟨henv, ?_⟩
  -- squeeze as `a ↓ 0`, with the fixed endpoint `b0 = amax/2`
  set b0 := amax / 2 with hb0
  have hb0mem : b0 ∈ Ioo 0 amax := ⟨by linarith, by linarith⟩
  set lb := (growthUpper (β b0 / ν) (m b0)).toReal with hlb
  have hlbpos : 0 < lb := (ereal_pos_fin (hpos b0 ⟨hb0mem.1.le, hb0mem.2⟩)
    (hfin b0 ⟨hb0mem.1.le, hb0mem.2⟩)).1
  set U : ℝ → ℝ := fun a => C * (lb / C) ^ (a / b0) with hU
  have hUt : Tendsto U (𝓝[>] 0) (𝓝 C) := by
    have hcont : Continuous U :=
      continuous_const.mul (continuous_const.rpow (continuous_id.div_const b0)
        fun _ => Or.inl (div_pos hlbpos hC).ne')
    have := hcont.continuousAt (x := 0)
    have hU0 : U 0 = C := by simp [hU]
    rw [← hU0]
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Ioo 0 b0 := Ioo_mem_nhdsGT hb0mem.1
  have hbounds : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      C ≤ (growthLower (β a / ν) (m a)).toReal ∧
        (growthLower (β a / ν) (m a)).toReal ≤ (growthUpper (β a / ν) (m a)).toReal ∧
        (growthUpper (β a / ν) (m a)).toReal ≤ U a ∧
        (((growthLower (β a / ν) (m a)).toReal : ℝ) : EReal) = growthLower (β a / ν) (m a) ∧
        (((growthUpper (β a / ν) (m a)).toReal : ℝ) : EReal) = growthUpper (β a / ν) (m a) := by
    filter_upwards [hev] with a ha
    obtain ⟨h1, h2, h3⟩ := henv b0 hb0mem a ha
    obtain ⟨hl1, hl2, hl3⟩ := ereal_toReal_between h1 (h2.trans h3)
    obtain ⟨hu1, hu2, hu3⟩ := ereal_toReal_between (h1.trans h2) h3
    refine ⟨hl1, ?_, hu2, hl3, hu3⟩
    rw [← hl3, ← hu3] at h2
    exact EReal.coe_le_coe_iff.1 h2
  have hlowR : Tendsto (fun a => (growthLower (β a / ν) (m a)).toReal) (𝓝[>] 0) (𝓝 C) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUt
      (hbounds.mono fun a h => h.1) (hbounds.mono fun a h => h.2.1.trans h.2.2.1)
  have hupR : Tendsto (fun a => (growthUpper (β a / ν) (m a)).toReal) (𝓝[>] 0) (𝓝 C) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUt
      (hbounds.mono fun a h => h.1.trans h.2.1) (hbounds.mono fun a h => h.2.2.1)
  refine ⟨?_, ?_, hlowR, hupR⟩
  · refine ((continuous_coe_real_ereal.tendsto C).comp hlowR).congr' ?_
    exact hbounds.mono fun a h => h.2.2.2.1
  · refine ((continuous_coe_real_ereal.tendsto C).comp hupR).congr' ?_
    exact hbounds.mono fun a h => h.2.2.2.2

/-! ### The manuscript's parameters (main TeX lines 7062-7069) -/

/-- `ν = 3 - α` (main TeX line 7065). -/
def nuOf (alpha : ℝ) : ℝ := 3 - alpha

/-- `a_max = min(1, 2 - α)` (main TeX line 7065). -/
def amaxOf (alpha : ℝ) : ℝ := min 1 (2 - alpha)

/-- `β(a) = 4 - α - a` (main TeX line 7066). -/
def betaOf (alpha a : ℝ) : ℝ := 4 - alpha - a

/-- `κ(a) = β(a)/ν` (main TeX line 7067). -/
def kappaOf (alpha a : ℝ) : ℝ := betaOf alpha a / nuOf alpha

/-- `κ_st = (4 - α)/ν` (main TeX line 7068). -/
def kappaSt (alpha : ℝ) : ℝ := (4 - alpha) / nuOf alpha

/-- Auxiliary (Lean route): `κ(0) = κ_st`. -/
theorem kappaOf_zero (alpha : ℝ) : kappaOf alpha 0 = kappaSt alpha := by
  simp [kappaOf, kappaSt, betaOf]

/-- Auxiliary (Lean route): for `α < 2`, `ν ≥ 1`, `a_max > 0`, and
`β(a) > 0` for `0 ≤ a < a_max`. -/
theorem params_of_lt_two {alpha : ℝ} (h : alpha < 2) :
    1 ≤ nuOf alpha ∧ 0 < amaxOf alpha ∧ ∀ a ∈ Ico 0 (amaxOf alpha), 0 < betaOf alpha a := by
  refine ⟨by simp only [nuOf]; linarith, lt_min one_pos (by linarith), fun a ha => ?_⟩
  have := lt_min_iff.1 ha.2
  simp only [betaOf]; linarith [this.2]

/-! ### The named inputs -/

/-- The inputs of `P:moment-growth-logconvex` and
`C:static-moment-constant-continuity` that are not formalized here, for the
moments `mom p a T = E[u^{(a)}(T,x)^p]` at a fixed point `x` (`p = 1, 2`;
`mom p 0` is the static moment `E[U(T,x)^p]`, main TeX lines 7070-7074) and the
full-moment coefficients `c p a k = c_{p,k}(a)` of
`E:full-moment-coefficients`. Each field is no stronger than its manuscript
source:
* `L0_pos`, `static_law`: the imported static law `E:static-ratio-input`
  (Chen-Hu, main TeX lines 7079-7087): `0 < L_0 < ∞` and
  `T^{-κ_st} log E U(T,x)^p → p^{κ_st} L_0` for `p = 1, 2`, verbatim.
* `series`: `E:full-moment-positive-series` with nonnegative coefficients
  and `c_{p,0}(a) = 1` (the definition `E:full-moment-coefficients`), from
  `L:full-moment-coefficient-holder` (main TeX lines 7433-7439), for
  `0 ≤ a < a_max`; the convergence `< ∞` is stated as summability.
* `holder`: `E:full-moment-coefficient-holder` (main TeX lines 7440-7444),
  verbatim.
* `minorant`: `E:static-minorant-rate` of `P:static-minorant-lower` (main TeX
  lines 7271-7275), `liminf ≥ p^{κ_st} L_0`, in the equivalent real form
  "every `y < p^{κ_st} L_0` is eventually below the normalized logarithm".
* `full_upper`: `E:full-upper-bound` of `T:full-upper` (main TeX lines
  3758-3772) applied at temporal exponent `a` (as the TeX does at lines 7534 and
  7365-7366):
  `E u^{(a)}(T,x)^2 ≤ e (T+2)^d exp(C T^{κ(a)})` for `T ≥ 1`, with the
  manuscript's finite `C R_α^{1/(3-α)}` written as one finite constant `C`.
* `cauchy_schwarz`: `(E u)^2 ≤ E u^2` for the same solution (the
  Cauchy-Schwarz step at main TeX line 7535). -/
structure TypeContinuityInputs (d : ℕ) (alpha : ℝ) (mom : ℕ → ℝ → ℝ → ℝ)
    (c : ℕ → ℝ → ℕ → ℝ) (L0 : ℝ) : Prop where
  L0_pos : 0 < L0
  static_law : ∀ p : ℕ, (p = 1 ∨ p = 2) →
    Tendsto (fun T : ℝ => T ^ (-kappaSt alpha) * Real.log (mom p 0 T)) atTop
      (𝓝 ((p : ℝ) ^ kappaSt alpha * L0))
  series : ∀ p : ℕ, (p = 1 ∨ p = 2) → ∀ a ∈ Ico 0 (amaxOf alpha),
    (∀ k, 0 ≤ c p a k) ∧ c p a 0 = 1 ∧ ∀ t : ℝ, 0 < t →
      Summable (fun k => c p a k * (t ^ betaOf alpha a) ^ k) ∧
        mom p a t = ∑' k, c p a k * (t ^ betaOf alpha a) ^ k
  holder : ∀ p : ℕ, (p = 1 ∨ p = 2) → ∀ a1 a a2 : ℝ, 0 ≤ a1 → a1 < a → a < a2 →
    a2 < amaxOf alpha → ∀ k,
      c p a k ≤ c p a1 k ^ (1 - (a - a1) / (a2 - a1)) * c p a2 k ^ ((a - a1) / (a2 - a1))
  minorant : ∀ p : ℕ, (p = 1 ∨ p = 2) → ∀ a ∈ Ioo 0 (amaxOf alpha), ∀ y : ℝ,
    y < (p : ℝ) ^ kappaSt alpha * L0 →
      ∀ᶠ T in atTop, y ≤ T ^ (-kappaOf alpha a) * Real.log (mom p a T)
  full_upper : ∀ a ∈ Ioo 0 (amaxOf alpha), ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
    mom 2 a T ≤ Real.exp 1 * (T + 2) ^ d * Real.exp (C * T ^ kappaOf alpha a)
  cauchy_schwarz : ∀ a ∈ Ioo 0 (amaxOf alpha), ∀ T : ℝ, 0 < T →
    mom 1 a T ^ 2 ≤ mom 2 a T

/-- Auxiliary (Lean route): the moments are at least one for `T > 0` (from the
positive series with `c_0 = 1`). -/
theorem one_le_mom {d : ℕ} {alpha : ℝ} {mom : ℕ → ℝ → ℝ → ℝ} {c : ℕ → ℝ → ℕ → ℝ}
    {L0 : ℝ} (hin : TypeContinuityInputs d alpha mom c L0) {p : ℕ} (hp : p = 1 ∨ p = 2)
    {a : ℝ} (ha : a ∈ Ico 0 (amaxOf alpha)) {T : ℝ} (hT : 0 < T) : 1 ≤ mom p a T := by
  obtain ⟨hc, hc0, hs⟩ := hin.series p hp a ha
  obtain ⟨hsum, heq⟩ := hs T hT
  rw [heq]
  exact one_le_seriesSum hc hc0 (Real.rpow_nonneg hT.le _) hsum

/-- **Positivity and finiteness of the upper growth rates** (the first sentence
of `P:moment-growth-logconvex`, main TeX lines 7518-7519, proof 7531-7537),
from the named inputs: `Λ̄_p(0) = C_p := p^{κ_st} L_0` (static law),
`Λ̲_p(a) ≥ C_p` for `0 < a < a_max` (`P:static-minorant-lower`), finiteness for
`p = 2` from `T:full-upper` and for `p = 1` by Cauchy-Schwarz. Needs
`α < 2` (from `H:homog`). -/
theorem upper_rate_pos_fin {d : ℕ} {alpha : ℝ} (halpha : alpha < 2)
    {mom : ℕ → ℝ → ℝ → ℝ} {c : ℕ → ℝ → ℕ → ℝ} {L0 : ℝ}
    (hin : TypeContinuityInputs d alpha mom c L0) (p : ℕ) (hp : p = 1 ∨ p = 2) :
    (∀ a ∈ Ico 0 (amaxOf alpha), 0 < growthUpper (kappaOf alpha a) (mom p a) ∧
        growthUpper (kappaOf alpha a) (mom p a) < ⊤) ∧
      growthUpper (kappaOf alpha 0) (mom p 0) = (((p : ℝ) ^ kappaSt alpha * L0 : ℝ) : EReal) ∧
      ∀ a ∈ Ioo 0 (amaxOf alpha),
        (((p : ℝ) ^ kappaSt alpha * L0 : ℝ) : EReal) ≤ growthLower (kappaOf alpha a) (mom p a) := by
  obtain ⟨hν, hamax, hβ⟩ := params_of_lt_two halpha
  have hp0 : (0 : ℝ) < p := by rcases hp with rfl | rfl <;> norm_num
  set Cp : ℝ := (p : ℝ) ^ kappaSt alpha * L0 with hCp
  have hCpos : 0 < Cp := mul_pos (Real.rpow_pos_of_pos hp0 _) hin.L0_pos
  have hκ : ∀ a ∈ Ico 0 (amaxOf alpha), 0 < kappaOf alpha a := fun a ha =>
    div_pos (hβ a ha) (by linarith)
  -- the static endpoint
  have h0 : growthUpper (kappaOf alpha 0) (mom p 0) = (Cp : EReal) := by
    unfold growthUpper
    rw [kappaOf_zero]
    exact ((continuous_coe_real_ereal.tendsto _).comp (hin.static_law p hp)).limsup_eq
  -- the lower bounds
  have hlow : ∀ a ∈ Ioo 0 (amaxOf alpha),
      (Cp : EReal) ≤ growthLower (kappaOf alpha a) (mom p a) := fun a ha =>
    le_liminf_of_forall_lt _ Cp fun y hy => hin.minorant p hp a ha y hy
  -- finiteness for positive exponents: an eventual real bound
  have hbd2 : ∀ a ∈ Ioo 0 (amaxOf alpha), ∃ B : ℝ, ∀ᶠ T in atTop,
      T ^ (-kappaOf alpha a) * Real.log (mom 2 a T) ≤ B := by
    intro a ha
    have haI : a ∈ Ico 0 (amaxOf alpha) := ⟨ha.1.le, ha.2⟩
    have hk := hκ a haI
    obtain ⟨C, hC⟩ := hin.full_upper a ha
    refine ⟨C + 1, ?_⟩
    have hlim := tendsto_rpow_neg_mul_affine_log hk (1 + d * Real.log 3) d
    filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually (ge_mem_nhds one_pos)]
      with T hT hsmall
    have hT0 : 0 < T := by linarith
    have hm1 := one_le_mom hin (Or.inr rfl) haI hT0
    have hlog : Real.log (mom 2 a T) ≤
        (1 + d * Real.log 3 + d * Real.log T) + C * T ^ kappaOf alpha a := by
      have h1 := Real.log_le_log (by linarith) (hC T hT)
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_exp, Real.log_exp, Real.log_pow] at h1
      have h2 : Real.log (T + 2) ≤ Real.log 3 + Real.log T := by
        rw [← Real.log_mul (by norm_num) hT0.ne']
        exact Real.log_le_log (by linarith) (by linarith)
      have h3 : (d : ℝ) * Real.log (T + 2) ≤ d * (Real.log 3 + Real.log T) := by gcongr
      linarith
    have hpos : 0 < T ^ (-kappaOf alpha a) := Real.rpow_pos_of_pos hT0 _
    have hcancel : T ^ (-kappaOf alpha a) * T ^ kappaOf alpha a = 1 := by
      rw [← Real.rpow_add hT0, neg_add_cancel, Real.rpow_zero]
    have h4 := mul_le_mul_of_nonneg_left hlog hpos.le
    have e : T ^ (-kappaOf alpha a) * ((1 + d * Real.log 3 + d * Real.log T) +
        C * T ^ kappaOf alpha a) =
        T ^ (-kappaOf alpha a) * ((1 + d * Real.log 3) + d * Real.log T) +
          C * (T ^ (-kappaOf alpha a) * T ^ kappaOf alpha a) := by ring
    rw [e, hcancel] at h4
    linarith
  have hbd : ∀ a ∈ Ioo 0 (amaxOf alpha), ∃ B : ℝ, ∀ᶠ T in atTop,
      T ^ (-kappaOf alpha a) * Real.log (mom p a T) ≤ B := by
    intro a ha
    rcases hp with rfl | rfl
    · obtain ⟨B, hB⟩ := hbd2 a ha
      refine ⟨B / 2, ?_⟩
      filter_upwards [hB, eventually_gt_atTop (0 : ℝ)] with T hTB hT0
      have haI : a ∈ Ico 0 (amaxOf alpha) := ⟨ha.1.le, ha.2⟩
      have hm1 := one_le_mom hin (Or.inl rfl) haI hT0
      have hcs := hin.cauchy_schwarz a ha T hT0
      have hlog : 2 * Real.log (mom 1 a T) ≤ Real.log (mom 2 a T) := by
        have := Real.log_le_log (by positivity) hcs
        rwa [Real.log_pow] at this
      have hpos : 0 ≤ T ^ (-kappaOf alpha a) := Real.rpow_nonneg hT0.le _
      have := mul_le_mul_of_nonneg_left hlog hpos
      linarith
    · exact hbd2 a ha
  refine ⟨fun a ha => ?_, h0, hlow⟩
  rcases ha.1.eq_or_lt with h | h
  · subst h
    rw [h0]
    exact ⟨EReal.coe_pos.2 hCpos, EReal.coe_lt_top _⟩
  · have haIoo : a ∈ Ioo 0 (amaxOf alpha) := ⟨h, ha.2⟩
    refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le (EReal.coe_pos.2 hCpos)
        ((hlow a haIoo).trans (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)))
    · obtain ⟨B, hB⟩ := hbd a haIoo
      have : growthUpper (kappaOf alpha a) (mom p a) ≤ (B : EReal) :=
        limsup_le_of_le (by isBoundedDefault) (hB.mono fun T hT => EReal.coe_le_coe_iff.2 hT)
      exact lt_of_le_of_lt this (EReal.coe_lt_top _)

/-! ### The manuscript statements -/

/-- Auxiliary (Lean route): `α < 2` under `H:homog` (from `α₀ + α < 2`,
`α₀ > 0`). -/
theorem alpha_lt_two {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) : alpha < 2 := by
  linarith [h.threshold, h.alpha0_pos]

/-- **`P:moment-growth-logconvex`** (Log-convexity of the upper growth type;
main TeX lines 7516-7528, proof 7530-7572), under the section's standing
assumptions (main TeX lines 7062-7069, 7423): a nonzero spatial covariance in
`H:homog` (`HomogCovariance`, `Γ ≠ 0`; both carried, only `α < 2` is used),
`ν = 3 - α`, `a_max = min(1, 2-α)`, `β(a) = 4-α-a`, `κ(a) = β(a)/ν`, and the
named inputs `TypeContinuityInputs` (see there for each input's manuscript
source). For `p = 1, 2` and `Λ̄_p(a) = growthUpper (κ(a)) (mom p a)`:
`Λ̄_p` is positive and finite on `[0, a_max)`; `E:moment-growth-logconvex`
holds for `0 ≤ a1 < a < a2 < a_max`, stated for the real values
`(Λ̄_p ·).toReal`, which are the rates by the finiteness just stated;
`log Λ̄_p` is convex on `[0, a_max)`; `Λ̄_p` and `log Λ̄_p` are continuous on
`(0, a_max)`. The identification of the type of `F_{p,a}` with `Λ̄_p(a)`
through `z = T^{β(a)}` is proved (`growthUpper_eq_seriesType`), not supplied.
Continuity is proved with `ConvexOn.continuousOn_interior` instead of the
TeX's secant slopes. Moments are at a fixed point `x`, so the spatial
stationarity used at main TeX line 7541 is not needed. -/
theorem moment_growth_logconvex_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0)
    (mom : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℝ → ℕ → ℝ) (L0 : ℝ)
    (hin : TypeContinuityInputs d alpha mom c L0) (p : ℕ) (hp : p = 1 ∨ p = 2) :
    (∀ a ∈ Ico 0 (amaxOf alpha), 0 < growthUpper (kappaOf alpha a) (mom p a) ∧
        growthUpper (kappaOf alpha a) (mom p a) < ⊤) ∧
      (∀ a1 a a2 : ℝ, 0 ≤ a1 → a1 < a → a < a2 → a2 < amaxOf alpha →
        (growthUpper (kappaOf alpha a) (mom p a)).toReal ≤
          (growthUpper (kappaOf alpha a1) (mom p a1)).toReal ^ (1 - (a - a1) / (a2 - a1)) *
            (growthUpper (kappaOf alpha a2) (mom p a2)).toReal ^ ((a - a1) / (a2 - a1))) ∧
      ConvexOn ℝ (Ico 0 (amaxOf alpha))
        (fun a => Real.log (growthUpper (kappaOf alpha a) (mom p a)).toReal) ∧
      ContinuousOn (fun a => (growthUpper (kappaOf alpha a) (mom p a)).toReal)
        (Ioo 0 (amaxOf alpha)) ∧
      ContinuousOn (fun a => Real.log (growthUpper (kappaOf alpha a) (mom p a)).toReal)
        (Ioo 0 (amaxOf alpha)) := by
  have halpha := alpha_lt_two h
  obtain ⟨hν, -, hβ⟩ := params_of_lt_two halpha
  obtain ⟨hpf, -, -⟩ := upper_rate_pos_fin halpha hin p hp
  exact ⟨hpf, growth_logconvex_core hν (betaOf alpha) hβ (mom p) (c p) (hin.series p hp)
    (hin.holder p hp) (fun a ha => (hpf a ha).1) (fun a ha => (hpf a ha).2)⟩

/-- **`C:static-moment-constant-continuity`** (Recovery of the static moment
constant; main TeX lines 7574-7593, proof 7595-7606), under the same standing
assumptions and named inputs as `moment_growth_logconvex_paper` (its own
inputs being `P:static-minorant-lower` and `Λ̄_p(0) = C_p`, both derived from
`TypeContinuityInputs`). With `C_p = p^{κ_st} L_0`, `Λ̲_p(a) =
growthLower (κ(a)) (mom p a)` and `Λ̄_p(a) = growthUpper (κ(a)) (mom p a)`,
for `p = 1, 2`: the envelope `E:static-constant-envelope` for
`0 < a < b < a_max` (in `EReal`, with `Λ̄_p(b)` finite and replaced by its
`toReal`); `E:static-constant-continuity` `Λ̲_p(a), Λ̄_p(a) → C_p` as
`a ↓ 0`; and `E:static-moment-ratio-continuity`
`Λ̲_2(a)/Λ̄_1(a) → 2^{κ_st}`, stated for the real values (finite and
positive by the envelope). -/
theorem static_moment_constant_continuity_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0)
    (mom : ℕ → ℝ → ℝ → ℝ) (c : ℕ → ℝ → ℕ → ℝ) (L0 : ℝ)
    (hin : TypeContinuityInputs d alpha mom c L0) :
    (∀ p : ℕ, (p = 1 ∨ p = 2) →
      (∀ b ∈ Ioo 0 (amaxOf alpha), ∀ a ∈ Ioo 0 b,
        (((p : ℝ) ^ kappaSt alpha * L0 : ℝ) : EReal) ≤ growthLower (kappaOf alpha a) (mom p a) ∧
          growthLower (kappaOf alpha a) (mom p a) ≤ growthUpper (kappaOf alpha a) (mom p a) ∧
          growthUpper (kappaOf alpha a) (mom p a) ≤
            (((p : ℝ) ^ kappaSt alpha * L0) *
              ((growthUpper (kappaOf alpha b) (mom p b)).toReal /
                ((p : ℝ) ^ kappaSt alpha * L0)) ^ (a / b) : ℝ)) ∧
        Tendsto (fun a => growthLower (kappaOf alpha a) (mom p a)) (𝓝[>] 0)
          (𝓝 (((p : ℝ) ^ kappaSt alpha * L0 : ℝ) : EReal)) ∧
        Tendsto (fun a => growthUpper (kappaOf alpha a) (mom p a)) (𝓝[>] 0)
          (𝓝 (((p : ℝ) ^ kappaSt alpha * L0 : ℝ) : EReal))) ∧
      Tendsto (fun a => (growthLower (kappaOf alpha a) (mom 2 a)).toReal /
          (growthUpper (kappaOf alpha a) (mom 1 a)).toReal) (𝓝[>] 0)
        (𝓝 ((2 : ℝ) ^ kappaSt alpha)) := by
  have halpha := alpha_lt_two h
  obtain ⟨hν, hamax, hβ⟩ := params_of_lt_two halpha
  have hcore : ∀ p : ℕ, (p = 1 ∨ p = 2) → _ := fun p hp => by
    obtain ⟨hpf, h0, hlow⟩ := upper_rate_pos_fin halpha hin p hp
    have hp0 : (0 : ℝ) < p := by rcases hp with rfl | rfl <;> norm_num
    exact static_constant_core hν hamax (betaOf alpha) hβ (mom p) (c p) (hin.series p hp)
      (hin.holder p hp) (fun a ha => (hpf a ha).1) (fun a ha => (hpf a ha).2)
      ((p : ℝ) ^ kappaSt alpha * L0) (mul_pos (Real.rpow_pos_of_pos hp0 _) hin.L0_pos) h0 hlow
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨henv, hl, hu, -, -⟩ := hcore p hp
    exact ⟨henv, hl, hu⟩
  · obtain ⟨-, -, -, hl2, -⟩ := hcore 2 (Or.inr rfl)
    obtain ⟨-, -, -, -, hu1⟩ := hcore 1 (Or.inl rfl)
    have hL := hin.L0_pos
    have hdiv := hl2.div hu1 (by simp; exact hL.ne')
    have e : ((2 : ℕ) : ℝ) ^ kappaSt alpha * L0 / (((1 : ℕ) : ℝ) ^ kappaSt alpha * L0) =
        (2 : ℝ) ^ kappaSt alpha := by
      simp only [Nat.cast_ofNat, Nat.cast_one, Real.one_rpow, one_mul]
      field_simp
    rw [e] at hdiv
    exact hdiv

end StratonovichHAMSecondMoment.TypeContinuity
