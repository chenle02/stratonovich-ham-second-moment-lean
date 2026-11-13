module

public import Mathlib

/-!
# Scalar power estimates (manuscript `L:gaussian-scalar-powers`)

Source: `notes/integrated_compact_gaussian.tex` at commit `ba01d98`, Lemma
`L:gaussian-scalar-powers` (statement lines 13--28, proof lines 30--48).

* `weighted_power`     -- (E:gaussian-weighted-power), weighted AM--GM.
* `integer_power`      -- (E:gaussian-integer-power), natural-number powers.
* `finite_holder`      -- finite Hölder with exponents `m` and `m/(m-1)`.
* `expectation_rpow_le` -- `E Z^r ≤ F^r` for `Z ≥ 0`, `F = E Z`, `0 < r < 1`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory

namespace StratonovichHAMSecondMoment.GaussianScalarPowers

/-- Part (1), (E:gaussian-weighted-power): for `0 < θ < 1` and `u, v ≥ 0`,
`u^θ v^(1-θ) ≤ θ u + (1-θ) v` (real powers). -/
theorem weighted_power (θ u v : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ θ * v ^ (1 - θ) ≤ θ * u + (1 - θ) * v :=
  Real.geom_mean_le_arith_mean2_weighted hθ0.le (by linarith) hu hv (by ring)

/-- Part (2), (E:gaussian-integer-power): for integers `L > 0`, `0 ≤ q ≤ L` and real
`x, y`, `|x|^q |y|^(L-q) ≤ (q/L)|x|^L + ((L-q)/L)|y|^L` (natural-number powers,
so `a^0 = 1`). -/
theorem integer_power (L q : ℕ) (hL : 0 < L) (hqL : q ≤ L) (x y : ℝ) :
    |x| ^ q * |y| ^ (L - q) ≤
      (q : ℝ) / L * |x| ^ L + ((L : ℝ) - q) / L * |y| ^ L := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simp [hLpos.ne']
  rcases eq_or_lt_of_le hqL with rfl | hqlt
  · simp [hLpos.ne']
  -- 0 < q < L: apply `weighted_power` with θ = q/L, u = |x|^L, v = |y|^L.
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqltR : (q : ℝ) < L := by exact_mod_cast hqlt
  set θ : ℝ := (q : ℝ) / L with hθ
  have hθ0 : 0 < θ := div_pos hqpos hLpos
  have hθ1 : θ < 1 := (div_lt_one hLpos).2 hqltR
  have key := weighted_power θ (|x| ^ L) (|y| ^ L) hθ0 hθ1 (by positivity) (by positivity)
  have h1 : (|x| ^ L) ^ θ = |x| ^ q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x), hθ,
      mul_div_cancel₀ _ hLpos.ne', Real.rpow_natCast]
  have h2 : (|y| ^ L) ^ (1 - θ) = |y| ^ (L - q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg y), hθ,
      ← Real.rpow_natCast, Nat.cast_sub hqL]
    congr 1
    field_simp
  have h3 : 1 - θ = ((L : ℝ) - q) / L := by rw [hθ]; field_simp
  rw [h1, h2, h3] at key
  exact key

/-- Part (3), finite Hölder for nonnegative finite sequences with exponents `m` and
`m/(m-1)`, `m > 1`. -/
theorem finite_holder {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (m : ℝ) (hm : 1 < m)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∑ i ∈ s, a i * b i ≤
      (∑ i ∈ s, a i ^ m) ^ (1 / m) *
        (∑ i ∈ s, b i ^ (m / (m - 1))) ^ ((m - 1) / m) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hconj : m.HolderConjugate (m / (m - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hm, ?_⟩
    field_simp
    ring
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hconj ha hb
  have hexp : 1 / (m / (m - 1)) = (m - 1) / m := by field_simp
  rw [hexp] at h
  exact h

/-- Pointwise bound used for integrability in part (4): `z^r ≤ r z + (1 - r)`. -/
private lemma rpow_le_affine (z r : ℝ) (hz : 0 ≤ z) (hr0 : 0 < r) (hr1 : r < 1) :
    z ^ r ≤ r * z + (1 - r) := by
  have := weighted_power r z 1 hr0 hr1 hz zero_le_one
  simpa using this

/-- Part (4): if `Z ≥ 0` a.s. has finite expectation `F = E Z` (on a probability space)
and `0 < r < 1`, then `Z^r` is integrable and `E Z^r ≤ F^r`. -/
theorem expectation_rpow_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Integrable Z μ) (hZnn : 0 ≤ᵐ[μ] Z)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Integrable (fun ω => Z ω ^ r) μ ∧ ∫ ω, Z ω ^ r ∂μ ≤ (∫ ω, Z ω ∂μ) ^ r := by
  set F := ∫ ω, Z ω ∂μ with hF
  have hint : Integrable (fun ω => Z ω ^ r) μ := by
    refine Integrable.mono' ((hZ.const_mul r).add (integrable_const (1 - r)))
      (hZ.aestronglyMeasurable.aemeasurable.pow_const r).aestronglyMeasurable ?_
    filter_upwards [hZnn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hω r)]
    exact rpow_le_affine (Z ω) r hω hr0 hr1
  refine ⟨hint, ?_⟩
  have hF0 : 0 ≤ F := integral_nonneg_of_ae hZnn
  rcases eq_or_lt_of_le hF0 with hFz | hFpos
  · -- F = 0 gives Z = 0 a.s.
    have hZ0 : Z =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hZnn hZ).1 hFz.symm
    have : ∫ ω, Z ω ^ r ∂μ = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [hZ0] with ω hω
      simp [hω, Real.zero_rpow hr0.ne']
    rw [this, ← hFz, Real.zero_rpow hr0.ne']
  · -- F > 0: apply part (1) to u = Z/F, v = 1, θ = r, and integrate.
    have hpt : ∀ᵐ ω ∂μ, Z ω ^ r ≤ F ^ r * (r * (Z ω / F) + (1 - r)) := by
      filter_upwards [hZnn] with ω hω
      have h1 := rpow_le_affine (Z ω / F) r (div_nonneg hω hF0) hr0 hr1
      have h2 : Z ω ^ r = F ^ r * (Z ω / F) ^ r := by
        rw [Real.div_rpow hω hF0, mul_div_cancel₀]
        exact (Real.rpow_pos_of_pos hFpos r).ne'
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hF0 r)
    have hrhs : Integrable (fun ω => F ^ r * (r * (Z ω / F) + (1 - r))) μ :=
      (((hZ.div_const F).const_mul r).add (integrable_const (1 - r))).const_mul _
    calc ∫ ω, Z ω ^ r ∂μ ≤ ∫ ω, F ^ r * (r * (Z ω / F) + (1 - r)) ∂μ :=
          integral_mono_ae hint hrhs hpt
      _ = F ^ r * (r * (F / F) + (1 - r)) := by
          rw [integral_const_mul, integral_add ((hZ.div_const F).const_mul r)
            (integrable_const (1 - r)), integral_const_mul,
            integral_div, integral_const]
          simp [← hF]
      _ = F ^ r := by rw [div_self hFpos.ne']; ring

end StratonovichHAMSecondMoment.GaussianScalarPowers
