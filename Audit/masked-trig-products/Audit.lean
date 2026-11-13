module
import StratonovichHAMSecondMoment.MaskedTrigProducts
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.norm_sq_sum_le
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.norm_sq_sum_le
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.norm_sq_sum_le_inner
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.norm_sq_sum_le_inner
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.bracket
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.bracket
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.bracket_neg
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.bracket_neg
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.frequencyPair
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.frequencyPair
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.Trig
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.Trig
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.Trig.eval
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.Trig.eval
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.modeFn
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.modeFn
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.sgn
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.sgn
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.coef1
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.coef1
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.coef
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.coef
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.freq
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.freq
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.norm_coef1
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.norm_coef1
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.norm_coef
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.norm_coef
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.sum_norm_coef
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.sum_norm_coef
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.exp_sgn
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.exp_sgn
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.Trig.eval_expand
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.Trig.eval_expand
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.four_mode
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.four_mode
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.cos_cos_expand
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.cos_cos_expand
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.sin_sin_expand
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.sin_sin_expand
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.sin_cos_expand
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.sin_cos_expand
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.cos_sin_expand
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.cos_sin_expand
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn_eq
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn_eq
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn_mem
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn_mem
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.sum_bracket_freq
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.sum_bracket_freq
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.trig_product_bound_half
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.trig_product_bound_half
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.trig_product_bound
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.trig_product_bound
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.C₀
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.C₀
#check @StratonovichHAMSecondMoment.MaskedTrigProducts.masked_trig_products_paper
#print axioms StratonovichHAMSecondMoment.MaskedTrigProducts.masked_trig_products_paper
/-- Consumer: since `⟨x⟩ ≥ 1` and `a < 1`, `𝒬_h(r,ρ) ≤ 2`, so the paper bound
gives the frequency-uniform estimate `‖1_I A P_r Q_ρ‖_a² ≤ 2 C₀(a) h^{2-a}(M+hD)²`. -/
private theorem masked_uniform_consumer {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (a T s h : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T)
    (A : ℝ → ℂ) (hA : ContDiffOn ℝ 1 A (Set.Icc s (s + h)))
    (M D : ℝ)
    (hM : M = sSup ((fun t => ‖A t‖) '' Set.Icc s (s + h)))
    (hD : D = sSup ((fun t => ‖derivWithin A (Set.Icc s (s + h)) t‖) '' Set.Icc s (s + h)))
    (r ρ : ℝ) (hr : 0 ≤ r) (hρ : 0 ≤ ρ)
    (P Q : StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (V : Submodule ℂ (ℝ → ℂ)) (emb : V →ₗ[ℂ] E)
    (hmem : ∀ ω : ℝ,
      StratonovichHAMSecondMoment.MaskedTrigProducts.modeFn (Set.Icc s (s + h)) A ω ∈ V)
    (hmod : ∀ ω : ℝ, ‖emb ⟨StratonovichHAMSecondMoment.MaskedTrigProducts.modeFn
        (Set.Icc s (s + h)) A ω, hmem ω⟩‖ ^ 2 ≤
      StratonovichHAMSecondMoment.MaskedTrigProducts.C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 *
        StratonovichHAMSecondMoment.MaskedTrigProducts.bracket (h * ω) ^ (a - 1)) :
    ∃ hp : StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn
        (Set.Icc s (s + h)) A P Q r ρ ∈ V,
      ‖emb ⟨StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn
          (Set.Icc s (s + h)) A P Q r ρ, hp⟩‖ ^ 2 ≤
        2 * (StratonovichHAMSecondMoment.MaskedTrigProducts.C₀ a * h ^ (2 - a) *
          (M + h * D) ^ 2) := by
  obtain ⟨hp, hb⟩ :=
    StratonovichHAMSecondMoment.MaskedTrigProducts.masked_trig_products_paper a T s h ha0 ha1
      hT hh0 hh1 hs hsT A hA M D hM hD r ρ hr hρ P Q V emb hmem hmod
  refine ⟨hp, (hb hp).trans ?_⟩
  have hbr : ∀ x : ℝ,
      StratonovichHAMSecondMoment.MaskedTrigProducts.bracket x ^ (a - 1) ≤ 1 := fun x =>
    Real.rpow_le_one_of_one_le_of_nonpos
      (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg x])) (by linarith)
  have hF : StratonovichHAMSecondMoment.MaskedTrigProducts.frequencyPair a h r ρ ≤ 2 := by
    unfold StratonovichHAMSecondMoment.MaskedTrigProducts.frequencyPair
    linarith [hbr (h * (r - ρ)), hbr (h * (r + ρ))]
  have hK : 0 ≤ StratonovichHAMSecondMoment.MaskedTrigProducts.C₀ a * h ^ (2 - a) *
      (M + h * D) ^ 2 := by
    unfold StratonovichHAMSecondMoment.MaskedTrigProducts.C₀
    have h1a : 0 < 1 - a := by linarith
    exact mul_nonneg (mul_nonneg (div_pos (by norm_num) h1a).le
      (Real.rpow_nonneg hh0.le _)) (sq_nonneg _)
  have := mul_le_mul_of_nonneg_left hF hK
  linarith
#check @masked_uniform_consumer
#print axioms masked_uniform_consumer
/- No example instantiating `masked_uniform_consumer`: it needs a complex inner
product space with a linear inclusion of an accepted class `V` and the supplied
modulation input `hmod` for every real `ω` (the manuscript's
`L:masked-temporal-modulation`), which this package does not construct. The
coefficient identity is instantiated instead. -/
example : ∑ j : Bool × Bool,
    ‖StratonovichHAMSecondMoment.MaskedTrigProducts.coef
      StratonovichHAMSecondMoment.MaskedTrigProducts.Trig.cos
      StratonovichHAMSecondMoment.MaskedTrigProducts.Trig.sin j‖ = 1 :=
  StratonovichHAMSecondMoment.MaskedTrigProducts.sum_norm_coef _ _
