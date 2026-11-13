/-
Refutation for the Cauchy-Schwarz bound of the space-time form, package theorem
`StratonovichHAMSecondMoment.SpaceTimePositivity.stForm_sq_le`
(`F(Ψ,G)² ≤ F(Ψ,Ψ) F(G,G)`; step (c) of the S1Bdd route, auxiliary; the bound
`⟨Ψ,ρ_g⟩ ≤ √(v_Ψ A(g))` of `L:occupation-raw-square`,
`integrated_occupation_ceiling.tex` line 40 at a284420, rests on it).

Wrong variant: a better constant, `F(Ψ,G)² ≤ (1/2) F(Ψ,Ψ) F(G,G)`, under all hypotheses of
the package theorem.  Counterexample: `d = 1`, `Γ` = Lebesgue measure (locally finite, even,
spectral measure `δ_0`), `a = 1/2`, `Ψ = G = Φ` with `Φ(s,x) = χ(s) q(x)` for smooth bumps
`χ` (support in `(1/4,3/4)`) and `q`.  Then `B_Γ(Φ_s,Φ_t) = χ(s) χ(t) (∫ q)²` and, since
`|s-t|^{-1/2} ≥ 1` off the diagonal, `F(Φ,Φ) ≥ (∫_I χ)² (∫ q)² > 0`, so `F² ≤ F²/2` fails.
`cs_constant_contrast` is the package bound at the same point.  No junk-value reliance
(every integral is of an integrable function, `stIntegrand_integrable`; the diagonal is null).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpaceTimePositivity

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open StratonovichHAMSecondMoment HomogHypothesis SpatialFourierBound SpaceTimePositivity

namespace Refutations.SpaceTimePositivity.CS

/-- The time bump, supported in `(1/4, 3/4) ⊂ (0,1)`. -/
def chiB : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The space bump on `ℝ¹`, supported in the ball of radius `2`. -/
def qB : ContDiffBump (0 : Rd 1) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The separable test field `Φ(s,x) = χ(s) q(x)`. -/
def phiEx : ℝ × Rd 1 → ℝ := fun p => chiB p.1 * qB p.2

theorem phiEx_continuous : Continuous phiEx :=
  (chiB.continuous.comp continuous_fst).mul (qB.continuous.comp continuous_snd)

theorem phiEx_hasCompactSupport : HasCompactSupport phiEx := by
  refine HasCompactSupport.intro (chiB.hasCompactSupport.isCompact.prod
    qB.hasCompactSupport.isCompact) fun p hp => ?_
  simp only [phiEx]
  by_cases h1 : p.1 ∈ tsupport chiB
  · have h2 : p.2 ∉ tsupport qB := fun h2 => hp ⟨h1, h2⟩
    rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0` in the manuscript's convention. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

theorem leb_even : IsEven (volume : Measure (Rd 1)) := Measure.map_neg_eq_self _

theorem qB_zero {x : Rd 1} (hx : 2 < ‖x‖) : qB x = 0 :=
  qB.zero_of_le_dist (by rw [dist_zero_right]; exact hx.le)

/-- `B_Γ(q,q) = (∫ q)²` for `Γ` = Lebesgue measure. -/
theorem pair_qB : spatialPair (volume : Measure (Rd 1)) qB qB = (∫ x, qB x) * ∫ x, qB x := by
  rw [spatialPair_eq_conv volume qB.continuous qB.continuous (A := 1) (B := 1) (R := 2)
    (fun x => by rw [abs_of_nonneg qB.nonneg]; exact qB.le_one)
    (fun x => by rw [abs_of_nonneg qB.nonneg]; exact qB.le_one)
    (fun x hx => qB_zero hx) (fun x hx => qB_zero hx)]
  simp only [VariationalDilation.conv]
  simp_rw [integral_sub_left_eq_self (fun y => qB y)]
  rw [integral_mul_const]

theorem stPair_phiEx (p : ℝ × ℝ) :
    stPair (volume : Measure (Rd 1)) phiEx phiEx p =
      chiB p.1 * chiB p.2 * ((∫ x, qB x) * ∫ x, qB x) := by
  rw [← pair_qB]
  unfold stPair spatialPair phiEx
  have h : ∀ y : Rd 1, ∫ x, chiB p.1 * qB x * (chiB p.2 * qB (x - y)) =
      chiB p.1 * chiB p.2 * ∫ x, qB x * qB (x - y) := by
    intro y; rw [← integral_const_mul]; congr 1; funext x; ring
  simp_rw [h]
  rw [integral_const_mul]

theorem chiB_mem {s : ℝ} (hs : chiB s ≠ 0) : |s - 1 / 2| < 1 / 4 := by
  have := chiB.support_eq ▸ (Function.mem_support.2 hs)
  rw [Metric.mem_ball, Real.dist_eq] at this
  exact this

/-- The concrete value is positive: `F(Φ,Φ) > 0` for `Γ` = Lebesgue measure and `a = 1/2`. -/
theorem stForm_phiEx_pos : 0 < stForm (1 / 2) (volume : Measure (Rd 1)) phiEx phiEx := by
  set c : ℝ := (∫ x, qB x) * ∫ x, qB x with hc
  have hq : 0 < ∫ x, qB x := qB.integral_pos
  have hc0 : 0 < c := mul_pos hq hq
  have hχi : Integrable (fun s => chiB s) timeMeasure :=
    (chiB.continuous.integrable_of_hasCompactSupport chiB.hasCompactSupport).restrict
  have hχint : ∫ s, chiB s ∂timeMeasure = ∫ s, chiB s := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
    by_contra hne
    have := chiB_mem hne
    rw [abs_lt] at this
    exact hs ⟨by linarith, by linarith⟩
  have hχ : 0 < ∫ s, chiB s ∂timeMeasure := hχint ▸ chiB.integral_pos
  have hf : Integrable (fun p : ℝ × ℝ => chiB p.1 * chiB p.2 * c)
      (timeMeasure.prod timeMeasure) := (hχi.mul_prod hχi).mul_const c
  have hg := stIntegrand_integrable (a := 1 / 2) (by norm_num) (volume : Measure (Rd 1))
    phiEx_continuous phiEx_hasCompactSupport phiEx_continuous phiEx_hasCompactSupport
  have hdiag : ∀ᵐ p ∂(timeMeasure.prod timeMeasure), p.1 ≠ p.2 := by
    have := TimeCompletion.ae_ne_diag 1
    rwa [← timeMeasure_eq_Icc] at this
  have hle : (fun p : ℝ × ℝ => chiB p.1 * chiB p.2 * c) ≤ᵐ[timeMeasure.prod timeMeasure]
      fun p => TimeSchur.kern (1 / 2) (p.1 - p.2) * stPair volume phiEx phiEx p := by
    filter_upwards [hdiag] with p hp
    rw [stPair_phiEx p, ← hc]
    have hnn : 0 ≤ chiB p.1 * chiB p.2 * c :=
      mul_nonneg (mul_nonneg chiB.nonneg chiB.nonneg) hc0.le
    by_cases h1 : chiB p.1 = 0
    · simp [h1]
    by_cases h2 : chiB p.2 = 0
    · simp [h2]
    have e1 := abs_lt.1 (chiB_mem h1)
    have e2 := abs_lt.1 (chiB_mem h2)
    have hk : 1 ≤ TimeSchur.kern (1 / 2) (p.1 - p.2) := by
      unfold TimeSchur.kern
      refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.2 (sub_ne_zero.2 hp)) ?_
        (by norm_num)
      rw [abs_le]; constructor <;> linarith
    calc chiB p.1 * chiB p.2 * c = 1 * (chiB p.1 * chiB p.2 * c) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hk hnn
  have hmono := integral_mono_ae hf hg hle
  have hval : ∫ p, chiB p.1 * chiB p.2 * c ∂(timeMeasure.prod timeMeasure) =
      (∫ s, chiB s ∂timeMeasure) * (∫ s, chiB s ∂timeMeasure) * c := by
    rw [integral_mul_const, integral_prod_mul (fun s => chiB s) (fun s => chiB s)]
  rw [hval] at hmono
  exact (mul_pos (mul_pos hχ hχ) hc0).trans_le hmono


/-- The Cauchy-Schwarz bound with the constant `1/2` is false. -/
theorem cs_constant_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)) [IsLocallyFiniteMeasure Γ], IsEven Γ → IsSpectralMeasure Γ μ →
        ∀ Ψ G : ℝ × Rd 1 → ℝ, Continuous Ψ → HasCompactSupport Ψ → Continuous G →
          HasCompactSupport G →
          stForm (1 / 2) Γ Ψ G ^ 2 ≤ 1 / 2 * (stForm (1 / 2) Γ Ψ Ψ * stForm (1 / 2) Γ G G)) := by
  intro h
  have h1 := h volume (Measure.dirac 0) leb_even leb_spectral phiEx phiEx phiEx_continuous
    phiEx_hasCompactSupport phiEx_continuous phiEx_hasCompactSupport
  have hp := stForm_phiEx_pos
  nlinarith [mul_pos hp hp]

/-- The package bound at the same point. -/
theorem cs_constant_contrast :
    stForm (1 / 2) (volume : Measure (Rd 1)) phiEx phiEx ^ 2 ≤
      stForm (1 / 2) volume phiEx phiEx * stForm (1 / 2) volume phiEx phiEx :=
  stForm_sq_le (by norm_num) (by norm_num) leb_even leb_spectral phiEx_continuous
    phiEx_hasCompactSupport phiEx_continuous phiEx_hasCompactSupport

end Refutations.SpaceTimePositivity.CS

end
