module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item D (part 2 of 2): Steps 4-5 of `L:spatial-wick-measures` and the whole lemma.
TeX lines 1679-1694 (statement) and 1802-1847 (Steps 4-5) at revision edf7085f (book 1.1.3)
of `notes/notes_stratonovich_ham_second_moment.tex`.

Main results (signatures frozen in `docs/l18/INTERFACE.md`, section 2 "D"):
* `spatial_wick_weak_limit (hB) (hC) : SpatialWickWeakLimitTarget d` (Step 4, 1802-1820);
* `spatial_wick_measures_of_weak (hW) (hB) (hC) (hS) : SpatialWickMeasuresTarget d` (Step 5,
  1824-1847, and local finiteness 1683);
* `spatial_wick_measures (hB) (hC) (hS) : SpatialWickMeasuresTarget d` (the whole lemma).
The hypotheses are other items' frozen targets: `hB : SpatialPositiveLaplaceTarget d` (item B,
`E:spatial-positive-laplace`, 1710-1719), `hC : WickMassBoundTarget d` (item C, 1795-1798),
`hS : RhoScalingTarget d` (item C, 1831-1838).  They are discharged at integration.

Route (disclosed differences from the TeX).
* Step 4: the abstract argument `WickStep4.step4` (pushforward by `y = e^{-r}`, Prokhorov on
  the cube, moment uniqueness by Stone-Weierstrass, no mass at the `y`-zero faces from
  continuity at zero, pullback by the cutoff argument).  The limits `L_D(λ)` are the `ε = 0`
  spectral integrals `limL`, reached by dominated convergence along the width filter itself
  (the TeX's monotone convergence, 1804-1805, is not needed: the integrand at `ε` is at most
  the one at `ε = 0`, whose integral is finite by Fatou and `hC`).  The convergence is along
  `widthFilter` directly; no reduction to sequences (1819-1820).
* Homogeneity (1837-1838, "passing to vague limits"): through Laplace transforms instead of
  vague limits.  For `c > 0` the finite measures `e^{-(c+1)Σr}·(ρ_D ∘ c)` and
  `e^{-(c+1)Σr}·c^{(4-α)k}ρ_D` have the same integer Laplace transforms (from `hS` at every
  positive width and the weak limit along `ε` and along `ε/c²`), hence are equal
  (`WickStep4.ext_of_laplace`).
* Horizon faces (1838-1843): the TeX's compact dilates are replaced by a countability argument:
  the level sets `{ℓ_i = T}`, `T > 0`, are disjoint, so only countably many carry `ν_D`-mass;
  homogeneity moves positive mass from one level to every level `T > 0`.
* `E:spatial-wick-limit` (1844-1847): the weak convergence is tested by
  `1_{ℓ_1<T_1, ℓ_2<T_2} e^{Σr} φ`, bounded (as `Σr = ℓ_1 + ℓ_2`) and continuous off the two
  horizon faces, which are `ν_D`-null (`WickStep4.tendsto_integral_of_null`).  The
  coordinate-zero faces are not needed for this step (they are proved separately, 1824-1828).
-/
public import StratonovichHAMSecondMoment.WickInterface
public import StratonovichHAMSecondMoment.WickStep4

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Real Pointwise BoundedContinuousFunction Nat

namespace StratonovichHAMSecondMoment.WickMeasures

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor)
open DiagramModel (Pi2 openers freq)
open WaveGreen (waveGreen)
open WickInterface
open WickStep4

variable {d : ℕ}

/-! ### The spectral integrands of `E:spatial-positive-laplace` -/

/-- The right side integrand of `E:spatial-positive-laplace` (TeX 1714-1717) at widths `ε`. -/
def lapInt (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (ε lam : Fin N → ℝ) (ξ : openers D → Rd d) :
    ℝ≥0∞ :=
  ENNReal.ofReal ((∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)) *
    ∏ l, 1 / ((1 + lam l) ^ 2 + ‖freq m D ξ l‖ ^ 2))

/-- The integrand at zero widths (all Gaussian factors equal to one). -/
def limInt (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (lam : Fin N → ℝ) (ξ : openers D → Rd d) :
    ℝ≥0∞ :=
  ENNReal.ofReal (∏ l, 1 / ((1 + lam l) ^ 2 + ‖freq m D ξ l‖ ^ 2))

/-- The limit transform `L_D(λ)` (TeX 1804-1805), as the spectral integral at zero widths. -/
def limL (μ : Measure (Rd d)) (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (lam : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, limInt m D lam ξ ∂Measure.pi fun _ : openers D => μ

/-- The Laplace integrand `e^{-Σ λ_l r_l}` of `wickL`. -/
def ex {N : ℕ} (lam : Fin N → ℝ) (r : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ i, lam i * r i))

lemma measurable_ex {N : ℕ} (lam : Fin N → ℝ) : Measurable (ex lam) := by
  unfold ex; fun_prop

lemma measurable_lapInt (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (ε lam : Fin N → ℝ) :
    Measurable (lapInt (d := d) m D ε lam) := by
  unfold lapInt gaussFactor freq; fun_prop

lemma measurable_limInt (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (lam : Fin N → ℝ) :
    Measurable (limInt (d := d) m D lam) := by
  unfold limInt freq; fun_prop

lemma factor_pos {N : ℕ} {lam : Fin N → ℝ} (hlam : ∀ l, 0 ≤ lam l) (l : Fin N) (x : ℝ)
    (hx : 0 ≤ x) : 0 < (1 + lam l) ^ 2 + x := by
  have := hlam l; positivity

lemma prod_factor_nonneg {N : ℕ} {lam : Fin N → ℝ} (hlam : ∀ l, 0 ≤ lam l) (v : Fin N → Rd d) :
    0 ≤ ∏ l, 1 / ((1 + lam l) ^ 2 + ‖v l‖ ^ 2) :=
  Finset.prod_nonneg fun l _ => (one_div_pos.2 (factor_pos hlam l _ (by positivity))).le

lemma lapInt_le (m : ℕ) {N : ℕ} (D : Fin N → Fin N) {ε lam : Fin N → ℝ} (hε : ∀ i, 0 ≤ ε i)
    (hlam : ∀ l, 0 ≤ lam l) (ξ : openers D → Rd d) : lapInt m D ε lam ξ ≤ limInt m D lam ξ := by
  unfold lapInt limInt
  refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (prod_factor_nonneg hlam _) ?_)
  refine Finset.prod_le_one₀ (fun e _ => (Real.exp_pos _).le) fun e _ => ?_
  unfold gaussFactor
  refine Real.exp_le_one_iff.2 (neg_nonpos.2 ?_)
  have := hε e; have := hε (D e); positivity

lemma limInt_anti (m : ℕ) {N : ℕ} (D : Fin N → Fin N) {lam : Fin N → ℝ} (hlam : ∀ l, 0 ≤ lam l)
    (ξ : openers D → Rd d) : limInt m D lam ξ ≤ limInt m D 0 ξ := by
  unfold limInt
  refine ENNReal.ofReal_le_ofReal (Finset.prod_le_prod₀ (fun l _ =>
    (one_div_pos.2 (factor_pos hlam l (‖freq m D ξ l‖ ^ 2) (by positivity))).le) fun l _ => ?_)
  refine one_div_le_one_div_of_le (factor_pos (fun _ => le_rfl) l (‖freq m D ξ l‖ ^ 2) (by positivity)) ?_
  have := hlam l
  simp only [Pi.zero_apply, add_zero, one_pow]
  nlinarith

lemma tendsto_lapInt (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (lam : Fin N → ℝ)
    (ξ : openers D → Rd d) :
    Tendsto (fun ε => lapInt m D ε lam ξ) (widthFilter N) (𝓝 (limInt m D lam ξ)) := by
  have hc : Continuous fun ε : Fin N → ℝ => lapInt m D ε lam ξ := by
    unfold lapInt gaussFactor; exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have h0 : lapInt m D (0 : Fin N → ℝ) lam ξ = limInt m D lam ξ := by
    simp [lapInt, limInt, gaussFactor]
  have := hc.tendsto 0
  rw [h0] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The width filter is countably generated. -/
instance instCountablyGeneratedWidthFilter (N : ℕ) : (widthFilter N).IsCountablyGenerated := by
  unfold widthFilter; infer_instance

/-- The positive widths are eventual along the width filter. -/
lemma eventually_pos (N : ℕ) : ∀ᶠ ε in widthFilter N, ∀ i, 0 < ε i := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa [posOrthant, Set.mem_univ_pi] using hε

section Spectral

variable {G : ℝ → Measure (Rd d)} {Γ μ : Measure (Rd d)} {m N : ℕ} {D : Fin N → Fin N}
  {C : ℝ≥0∞}

/-- `L_D(0) ≤ sup_ε L_{ε,D}(0)` (Fatou along the width filter). -/
theorem limL_zero_le
    (hBD : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) → ∀ lam : Fin N → ℝ, (∀ i, 0 ≤ lam i) →
      wickL G Γ ε m D lam = ∫⁻ ξ, lapInt m D ε lam ξ ∂Measure.pi fun _ : openers D => μ)
    (hCb : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) → wickL G Γ ε m D 0 ≤ C) :
    limL μ m D 0 ≤ C := by
  have hF := lintegral_liminf_le' (μ := Measure.pi fun _ : openers D => μ)
    (u := widthFilter N) (f := fun ε ξ => lapInt m D ε 0 ξ)
    (fun ε => (measurable_lapInt m D ε 0).aemeasurable)
  have hl : ∀ ξ : openers D → Rd d, liminf (fun ε => lapInt m D ε 0 ξ) (widthFilter N) = limInt m D 0 ξ :=
    fun ξ => (tendsto_lapInt m D 0 ξ).liminf_eq
  simp only [hl] at hF
  refine hF.trans (Filter.liminf_le_of_frequently_le' (Eventually.frequently ?_))
  filter_upwards [eventually_pos N] with ε hε
  rw [← hBD ε hε 0 fun _ => le_rfl]
  exact hCb ε hε

theorem limL_le_zero {lam : Fin N → ℝ} (hlam : ∀ l, 0 ≤ lam l) : limL μ m D lam ≤ limL μ m D 0 :=
  lintegral_mono fun ξ => limInt_anti m D hlam ξ

/-- `L_{ε,D}(λ) → L_D(λ)` along the width filter (dominated convergence). -/
theorem tendsto_wickL
    (hBD : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) → ∀ lam : Fin N → ℝ, (∀ i, 0 ≤ lam i) →
      wickL G Γ ε m D lam = ∫⁻ ξ, lapInt m D ε lam ξ ∂Measure.pi fun _ : openers D => μ)
    (hfin : limL μ m D 0 ≠ ∞) {lam : Fin N → ℝ} (hlam : ∀ l, 0 ≤ lam l) :
    Tendsto (fun ε => wickL G Γ ε m D lam) (widthFilter N) (𝓝 (limL μ m D lam)) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := Measure.pi fun _ : openers D => μ)
    (l := widthFilter N) (F := fun ε ξ => lapInt m D ε lam ξ) (f := limInt m D lam)
    (limInt m D 0)
    (Eventually.of_forall fun ε => measurable_lapInt m D ε lam)
    (by filter_upwards [eventually_pos N] with ε hε
        exact Eventually.of_forall fun ξ =>
          (lapInt_le m D (fun i => (hε i).le) hlam ξ).trans (limInt_anti m D hlam ξ))
    hfin (Eventually.of_forall fun ξ => tendsto_lapInt m D lam ξ)
  refine h.congr' ?_
  filter_upwards [eventually_pos N] with ε hε
  exact (hBD ε hε lam hlam).symm

/-- Continuity of `L_D` at zero along the diagonal (TeX 1805-1807). -/
theorem tendsto_limL_diag (hfin : limL μ m D 0 ≠ ∞) :
    Tendsto (fun c : ℝ => limL μ m D fun _ => c) (𝓝[>] 0) (𝓝 (limL μ m D 0)) := by
  refine tendsto_lintegral_filter_of_dominated_convergence (limInt m D 0)
    (Eventually.of_forall fun c => measurable_limInt m D _)
    (eventually_nhdsWithin_of_forall fun c hc => Eventually.of_forall fun ξ =>
      limInt_anti m D (fun _ => le_of_lt hc) ξ) hfin (Eventually.of_forall fun ξ => ?_)
  have hfac : ∀ l, Tendsto (fun c : ℝ => 1 / ((1 + c) ^ 2 + ‖freq m D ξ l‖ ^ 2)) (𝓝 0)
      (𝓝 (1 / ((1 + 0) ^ 2 + ‖freq m D ξ l‖ ^ 2))) := fun l =>
    ((continuousAt_const.div (by fun_prop) (by positivity)) :
      ContinuousAt (fun c : ℝ => 1 / ((1 + c) ^ 2 + ‖freq m D ξ l‖ ^ 2)) 0).tendsto
  have := (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_finsetProd Finset.univ fun l _ => hfac l)
  simpa [limInt, Function.comp_def] using this.mono_left nhdsWithin_le_nhds

/-- `L_D(t e_l) → 0` as `t → ∞` (TeX 1825-1827). -/
theorem tendsto_limL_single (hfin : limL μ m D 0 ≠ ∞) (l : Fin N) :
    Tendsto (fun t : ℝ => limL μ m D (Pi.single l t)) atTop (𝓝 0) := by
  have hnn : ∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ (Pi.single l t : Fin N → ℝ) i := fun t ht i => by
    by_cases h : i = l
    · subst h; simp [ht]
    · simp [Pi.single_eq_of_ne h]
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := Measure.pi fun _ : openers D => μ)
    (l := atTop) (F := fun t ξ => limInt m D (Pi.single l t) ξ) (f := fun _ => 0)
    (limInt m D 0) (Eventually.of_forall fun t => measurable_limInt m D _)
    (eventually_atTop.2 ⟨0, fun t ht => Eventually.of_forall fun ξ =>
      limInt_anti m D (hnn t ht) ξ⟩) hfin (Eventually.of_forall fun ξ => ?_)
  · simpa [limL] using h
  have hfac : ∀ l', Tendsto (fun t : ℝ => 1 / ((1 + (Pi.single l t : Fin N → ℝ) l') ^ 2 +
      ‖freq m D ξ l'‖ ^ 2)) atTop
      (𝓝 (if l' = l then 0 else 1 / ((1 + 0) ^ 2 + ‖freq m D ξ l'‖ ^ 2))) := fun l' => by
    by_cases h : l' = l
    · subst h
      simp only [Pi.single_eq_same, ↓reduceIte]
      have hden : Tendsto (fun t : ℝ => (1 + t) ^ 2 + ‖freq m D ξ l'‖ ^ 2) atTop atTop :=
        Filter.tendsto_atTop_add_const_right _ _ ((tendsto_pow_atTop two_ne_zero).comp
          (tendsto_atTop_add_const_left _ 1 tendsto_id))
      exact tendsto_const_nhds.div_atTop hden
    · simp only [Pi.single_eq_of_ne h, h, ↓reduceIte]
      exact tendsto_const_nhds
  have := (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_finsetProd Finset.univ fun l' _ => hfac l')
  have h0 : (∏ l' : Fin N, (if l' = l then (0 : ℝ) else 1 / ((1 + 0) ^ 2 + ‖freq m D ξ l'‖ ^ 2))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  rw [h0, ENNReal.ofReal_zero] at this
  simpa [limInt, Function.comp_def] using this

end Spectral

/-! ### The measures `ν_{ε,D}` -/

section Nu

variable {G : ℝ → Measure (Rd d)} {Γ : Measure (Rd d)} {m N : ℕ} {D : Fin N → Fin N}

/-- `ν_{ε,D}` is carried by the open orthant, hence by the closed one. -/
lemma wickNu_compl_nonneg (ε : Fin N → ℝ) : wickNu G Γ ε m D (nonneg N)ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ (withDensity_absolutelyContinuous _ _ ?_)
  rw [Measure.restrict_apply (measurableSet_nonneg N).compl]
  convert measure_empty (μ := (volume : Measure (Fin N → ℝ)))
  ext r
  simp only [mem_inter_iff, mem_compl_iff, posOrthant, Set.mem_univ_pi, mem_Ioi,
    mem_empty_iff_false, iff_false, not_and]
  intro hr hpos; exact hr (mem_nonneg.2 fun l => (hpos l).le)

lemma lintegral_lap_eq {P : Measure (Fin N → ℝ)} (hP : P (nonneg N)ᶜ = 0) (lam : Fin N → ℝ) :
    ∫⁻ r, ENNReal.ofReal (lap lam r) ∂P = ∫⁻ r, ex lam r ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_nonneg_of_null hP] with r hr
  rw [ex, lap_of_nonneg lam hr]

lemma integral_lap_eq {P : Measure (Fin N → ℝ)} (hP : P (nonneg N)ᶜ = 0) (lam : Fin N → ℝ) :
    ∫ r, lap lam r ∂P = (∫⁻ r, ex lam r ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => (lap_pos lam r).le)
    (continuous_lap lam).aestronglyMeasurable, lintegral_lap_eq hP]

lemma lintegral_ex_le {P : Measure (Fin N → ℝ)} (hP : P (nonneg N)ᶜ = 0) {lam : Fin N → ℝ}
    (hlam : ∀ l, 0 ≤ lam l) : ∫⁻ r, ex lam r ∂P ≤ P univ := by
  rw [← lintegral_lap_eq hP, ← lintegral_one]
  exact lintegral_mono fun r => by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (lap_le_one hlam r)

/-- The finite-measure family along positive widths (zero elsewhere). -/
def finFam {ι X : Type*} [MeasurableSpace X] (ν : ι → Measure X) (p : ι → Prop)
    (h : ∀ i, p i → IsFiniteMeasure (ν i)) : ι → FiniteMeasure X := fun i => by
  classical
  exact if hi : p i then ⟨ν i, h i hi⟩ else 0

lemma finFam_of {ι X : Type*} [MeasurableSpace X] (ν : ι → Measure X) (p : ι → Prop)
    (h : ∀ i, p i → IsFiniteMeasure (ν i)) {i : ι} (hi : p i) :
    (finFam ν p h i : Measure X) = ν i := by
  simp [finFam, hi]

lemma finFam_mass_le {ι X : Type*} [MeasurableSpace X] (ν : ι → Measure X) (p : ι → Prop)
    (h : ∀ i, p i → IsFiniteMeasure (ν i)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ i, p i → ν i univ ≤ C) (i : ι) : (finFam ν p h i).mass ≤ C.toNNReal := by
  classical
  by_cases hi : p i
  · rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, finFam_of ν p h hi,
      ENNReal.coe_toNNReal hC]
    exact hb i hi
  · simp [finFam, hi]

/-- Weak convergence (as integrals of bounded continuous functions) of `ν_{ε,D}` to `νD`, as
convergence of the finite-measure family. -/
lemma tendsto_finFam {νD : Measure (Fin N → ℝ)} [IsFiniteMeasure νD]
    (hfin : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) → IsFiniteMeasure (wickNu G Γ ε m D))
    (hW : ∀ phi : (Fin N → ℝ) →ᵇ ℝ, Tendsto (fun ε => ∫ r, phi r ∂wickNu G Γ ε m D)
      (widthFilter N) (𝓝 (∫ r, phi r ∂νD))) :
    Tendsto (finFam (fun ε => wickNu G Γ ε m D) (fun ε => ∀ i, 0 < ε i) hfin) (widthFilter N)
      (𝓝 (⟨νD, inferInstance⟩ : FiniteMeasure (Fin N → ℝ))) := by
  refine FiniteMeasure.tendsto_iff_forall_integral_tendsto.2 fun phi => ?_
  refine (hW phi).congr' ?_
  filter_upwards [eventually_pos N] with ε hε
  rw [finFam_of _ _ hfin hε]

end Nu

/-! ### Step 4: the weak limit (TeX 1802-1820) -/

/-- **Step 4 of `L:spatial-wick-measures`** (TeX lines 1802-1820 at revision edf7085f, book
1.1.3; the lemma's first sentence, 1680-1682): from `E:spatial-positive-laplace` (item B) and
the uniform mass bound (item C), the finite measures `ν_{ε,D}` converge weakly along the width
filter to a finite measure.  Route: `WickStep4.step4` with `L_D = limL` (see the module
docstring for the differences from the TeX). -/
theorem spatial_wick_weak_limit (d : ℕ) (hB : SpatialPositiveLaplaceTarget d)
    (hC : WickMassBoundTarget d) : SpatialWickWeakLimitTarget d := by
  intro alpha α₀ Γ μ hH m n k hmn hk D hD
  obtain ⟨C, hCfin, hCb⟩ := hC hH m n k hmn hk D hD
  have hBD : ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) → ∀ lam : Fin (m + n) → ℝ, (∀ i, 0 ≤ lam i) →
      wickL (waveGreen d) Γ ε m D lam =
        ∫⁻ ξ, lapInt m D ε lam ξ ∂Measure.pi fun _ : openers D => μ :=
    fun ε hε lam hlam => hB hH m n k hmn hk D hD ε hε lam hlam
  have hL0 : limL μ m D 0 ≠ ∞ := ((limL_zero_le hBD hCb).trans_lt hCfin).ne
  have hne : ∀ lam : Fin (m + n) → ℝ, (∀ l, 0 ≤ lam l) → limL μ m D lam ≠ ∞ := fun lam hlam =>
    ne_top_of_le_ne_top hL0 (limL_le_zero hlam)
  have hfin : ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) →
      IsFiniteMeasure (wickNu (waveGreen d) Γ ε m D) :=
    fun ε hε => ⟨by rw [← wickL_zero]; exact (hCb ε hε).trans_lt hCfin⟩
  obtain ⟨ν, hconv, -, -⟩ := step4 (F := widthFilter (m + n))
    (μs := finFam (fun ε => wickNu (waveGreen d) Γ ε m D) (fun ε => ∀ i, 0 < ε i) hfin)
    (C := C.toNNReal)
    (finFam_mass_le _ _ hfin hCfin.ne fun ε hε => by rw [← wickL_zero]; exact hCb ε hε)
    (by filter_upwards [eventually_pos _] with ε hε
        rw [finFam_of _ _ hfin hε]; exact wickNu_compl_nonneg ε)
    (Lim := fun lam => (limL μ m D lam).toReal)
    (fun lam hlam => by
      refine ((ENNReal.tendsto_toReal (hne lam hlam)).comp (tendsto_wickL hBD hL0 hlam)).congr' ?_
      filter_upwards [eventually_pos _] with ε hε
      rw [Function.comp_apply, finFam_of _ _ hfin hε, integral_lap_eq (wickNu_compl_nonneg ε)]
      rfl)
    ((ENNReal.tendsto_toReal hL0).comp (tendsto_limL_diag hL0))
  refine ⟨(ν : Measure _), inferInstance, hfin, fun phi => ?_⟩
  refine ((FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hconv) phi).congr' ?_
  filter_upwards [eventually_pos _] with ε hε
  rw [finFam_of _ _ hfin hε]

/-! ### Step 5: properties of the limit -/

section Limit

variable {N : ℕ}

lemma rhoLim_eq_zero_iff (νD : Measure (Fin N → ℝ)) (s : Set (Fin N → ℝ)) :
    rhoLim νD s = 0 ↔ νD s = 0 := by
  rw [rhoLim, withDensity_apply_eq_zero' (by fun_prop)]
  have : {x : Fin N → ℝ | ENNReal.ofReal (Real.exp (∑ i, x i)) ≠ 0} = univ := by
    ext x; simp [Real.exp_pos]
  rw [this, univ_inter]

/-- `ρ_D` is locally finite (TeX 1683; it follows from the finiteness of `ν_D`). -/
theorem rhoLim_locallyFinite (νD : Measure (Fin N → ℝ)) [IsFiniteMeasure νD] :
    IsLocallyFiniteMeasure (rhoLim νD) := by
  refine ⟨fun x => ?_⟩
  have ho : IsOpen {r : Fin N → ℝ | ∑ i, r i < ∑ i, x i + 1} :=
    isOpen_lt (by fun_prop) continuous_const
  refine ⟨_, ho.mem_nhds (by simp), ?_⟩
  rw [rhoLim, withDensity_apply _ ho.measurableSet]
  calc ∫⁻ r in {r : Fin N → ℝ | ∑ i, r i < ∑ i, x i + 1}, ENNReal.ofReal (Real.exp (∑ i, r i)) ∂νD
      ≤ ∫⁻ r in {r : Fin N → ℝ | ∑ i, r i < ∑ i, x i + 1},
          ENNReal.ofReal (Real.exp (∑ i, x i + 1)) ∂νD :=
        setLIntegral_mono' ho.measurableSet fun r hr =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_lt hr))
    _ < ∞ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- Level sets of a continuous homogeneous function at positive levels are null for `ν_D`, if
`ρ_D` is homogeneous (TeX 1838-1843; countability instead of compact dilates). -/
theorem level_null (νD : Measure (Fin N → ℝ)) [IsFiniteMeasure νD]
    {L : (Fin N → ℝ) → ℝ} (hLc : Continuous L) (hLh : ∀ (c : ℝ) (r : Fin N → ℝ), L (c • r) = c * L r)
    {κ : ℝ → ℝ≥0∞} (hκ : ∀ c, 0 < c → κ c ≠ 0)
    (hom : ∀ c : ℝ, 0 < c → ∀ A : Set (Fin N → ℝ), MeasurableSet A →
      rhoLim νD (c • A) = κ c * rhoLim νD A) {T : ℝ} (hT : 0 < T) :
    νD {r | L r = T} = 0 := by
  by_contra h0
  have hmeas : ∀ T' : ℝ, MeasurableSet {r : Fin N → ℝ | L r = T'} := fun T' =>
    measurableSet_eq_fun hLc.measurable measurable_const
  have hcount := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top νD
    (As := fun T' : ℝ => {r : Fin N → ℝ | L r = T'}) hmeas
    (fun a b hab => Set.disjoint_left.2 fun r h1 h2 => hab (h1.symm.trans h2))
    (measure_ne_top _ _)
  have hsub : Ioi (0 : ℝ) ⊆ {T' | 0 < νD {r | L r = T'}} := fun T' hT' => by
    have hc : 0 < T' / T := div_pos hT' hT
    have hset : (T' / T) • {r : Fin N → ℝ | L r = T} = {r | L r = T'} := by
      ext r
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
      simp only [Set.mem_ofPred_eq, hLh]
      rw [inv_mul_eq_iff_eq_mul₀ hc.ne', div_mul_cancel₀ T' hT.ne']
    have h1 : rhoLim νD {r | L r = T} ≠ 0 := fun h => h0 ((rhoLim_eq_zero_iff νD _).1 h)
    have h2 : rhoLim νD {r | L r = T'} ≠ 0 := by
      rw [← hset, hom _ hc _ (hmeas T)]; exact mul_ne_zero (hκ _ hc) h1
    exact pos_iff_ne_zero.2 fun h => h2 ((rhoLim_eq_zero_iff νD _).2 h)
  have := (hcount.mono hsub).measure_zero (volume : Measure ℝ)
  rw [Real.volume_Ioi] at this
  exact ENNReal.top_ne_zero this

lemma ell1_smul (m : ℕ) (c : ℝ) (r : Fin N → ℝ) : ell1 m (c • r) = c * ell1 m r := by
  simp [ell1, Finset.mul_sum]

lemma ell2_smul (m : ℕ) (c : ℝ) (r : Fin N → ℝ) : ell2 m (c • r) = c * ell2 m r := by
  simp [ell2, Finset.mul_sum]

lemma continuous_ell1 (m : ℕ) : Continuous (ell1 m : (Fin N → ℝ) → ℝ) := by
  unfold ell1; fun_prop

lemma continuous_ell2 (m : ℕ) : Continuous (ell2 m : (Fin N → ℝ) → ℝ) := by
  unfold ell2; fun_prop

lemma sum_eq_ell (m : ℕ) (r : Fin N → ℝ) : ∑ i, r i = ell1 m r + ell2 m r := by
  rw [ell1, ell2, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < m)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i; simp

lemma lap_single (l : Fin N) (t : ℝ) (r : Fin N → ℝ) :
    lap (Pi.single l t) r = Real.exp (-(t * max (r l) 0)) := by
  unfold lap
  congr 2
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

lemma ex_mul_ex {lam : Fin N → ℝ} (x : ℝ) (r : Fin N → ℝ) :
    ENNReal.ofReal (Real.exp x) * ex lam r = ENNReal.ofReal (Real.exp (x - ∑ i, lam i * r i)) := by
  rw [ex, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, sub_eq_add_neg]

end Limit

/-! ### Step 5 from the weak limit -/

section Weak

variable {G : ℝ → Measure (Rd d)} {Γ μ : Measure (Rd d)} {m N : ℕ} {D : Fin N → Fin N}
  {νD : Measure (Fin N → ℝ)} [IsFiniteMeasure νD]

/-- The test function `min 1 (Σ_l (-r_l) ∨ 0)`, zero exactly on the closed orthant. -/
def negPart (r : Fin N → ℝ) : ℝ := min 1 (∑ l, max (-(r l)) 0)

lemma negPart_nonneg (r : Fin N → ℝ) : 0 ≤ negPart r :=
  le_min zero_le_one (Finset.sum_nonneg fun _ _ => le_max_right _ _)

lemma continuous_negPart : Continuous (negPart : (Fin N → ℝ) → ℝ) := by
  unfold negPart; fun_prop

/-- The weak limit is carried by the closed orthant (portmanteau, TeX 1815-1817). -/
theorem nuD_supp
    (hWk : ∀ phi : (Fin N → ℝ) →ᵇ ℝ, Tendsto (fun ε => ∫ r, phi r ∂wickNu G Γ ε m D)
      (widthFilter N) (𝓝 (∫ r, phi r ∂νD))) :
    νD (nonneg N)ᶜ = 0 := by
  let ψ : (Fin N → ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup negPart
    continuous_negPart 1 fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negPart_nonneg r)]; exact min_le_left _ _
  have h0 : ∫ r, ψ r ∂νD = 0 := by
    refine tendsto_nhds_unique (hWk ψ) (tendsto_const_nhds.congr' (Eventually.of_forall fun ε => ?_))
    refine (integral_eq_zero_of_ae ?_).symm
    filter_upwards [ae_nonneg_of_null (wickNu_compl_nonneg (G := G) (Γ := Γ) (m := m) (D := D) ε)]
      with r hr
    simp only [ψ, BoundedContinuousFunction.coe_ofNormedAddCommGroup, negPart, Pi.zero_apply]
    rw [Finset.sum_eq_zero fun l _ => max_eq_right (neg_nonpos.2 (mem_nonneg.1 hr l)), min_eq_right zero_le_one]
  have hae := (integral_eq_zero_iff_of_nonneg (fun r => negPart_nonneg r) (ψ.integrable νD)).1 h0
  rw [EventuallyEq, ae_iff] at hae
  refine measure_mono_null (fun r hr => ?_) hae
  simp only [mem_compl_iff, mem_nonneg, not_forall, not_le] at hr
  obtain ⟨l, hl⟩ := hr
  simp only [Set.mem_ofPred_eq, Pi.zero_apply]
  refine ne_of_gt (lt_min zero_lt_one ?_)
  exact lt_of_lt_of_le (lt_max_of_lt_left (neg_pos.2 hl))
    (Finset.single_le_sum (f := fun l => max (-(r l)) 0) (fun l _ => le_max_right _ _)
      (Finset.mem_univ l))

/-- Laplace transforms converge against the weak limit (as real numbers). -/
theorem tendsto_ex
    (hWk : ∀ phi : (Fin N → ℝ) →ᵇ ℝ, Tendsto (fun ε => ∫ r, phi r ∂wickNu G Γ ε m D)
      (widthFilter N) (𝓝 (∫ r, phi r ∂νD)))
    {lam : Fin N → ℝ} (hlam : ∀ l, 0 ≤ lam l) :
    Tendsto (fun ε => (∫⁻ r, ex lam r ∂wickNu G Γ ε m D).toReal) (widthFilter N)
      (𝓝 ((∫⁻ r, ex lam r ∂νD).toReal)) := by
  have h := hWk (lapB lam hlam)
  simp only [lapB_apply] at h
  rw [integral_lap_eq (nuD_supp hWk)] at h
  refine h.congr' (Eventually.of_forall fun ε => ?_)
  rw [integral_lap_eq (wickNu_compl_nonneg ε)]

/-- The Laplace transform of the weak limit is `L_D` (TeX 1810-1811). -/
theorem nuD_ex
    (hWk : ∀ phi : (Fin N → ℝ) →ᵇ ℝ, Tendsto (fun ε => ∫ r, phi r ∂wickNu G Γ ε m D)
      (widthFilter N) (𝓝 (∫ r, phi r ∂νD)))
    (hBD : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) → ∀ lam : Fin N → ℝ, (∀ i, 0 ≤ lam i) →
      wickL G Γ ε m D lam = ∫⁻ ξ, lapInt m D ε lam ξ ∂Measure.pi fun _ : openers D => μ)
    (hL0 : limL μ m D 0 ≠ ∞) {lam : Fin N → ℝ} (hlam : ∀ l, 0 ≤ lam l) :
    ∫⁻ r, ex lam r ∂νD = limL μ m D lam := by
  have hne : limL μ m D lam ≠ ∞ := ne_top_of_le_ne_top hL0 (limL_le_zero hlam)
  have h1 := tendsto_ex hWk hlam
  have h2 := (ENNReal.tendsto_toReal hne).comp (tendsto_wickL hBD hL0 hlam)
  have e := tendsto_nhds_unique h1 h2
  exact (ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top (measure_ne_top νD univ)
    (lintegral_ex_le (nuD_supp hWk) hlam)) hne).1 e

/-- **Zero gaps** (TeX 1824-1828): `ν_D{r_l = 0} = 0`. -/
theorem nuD_zero_face
    (hWk : ∀ phi : (Fin N → ℝ) →ᵇ ℝ, Tendsto (fun ε => ∫ r, phi r ∂wickNu G Γ ε m D)
      (widthFilter N) (𝓝 (∫ r, phi r ∂νD)))
    (hBD : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) → ∀ lam : Fin N → ℝ, (∀ i, 0 ≤ lam i) →
      wickL G Γ ε m D lam = ∫⁻ ξ, lapInt m D ε lam ξ ∂Measure.pi fun _ : openers D => μ)
    (hL0 : limL μ m D 0 ≠ ∞) (l : Fin N) :
    νD {r | r l = 0} = 0 := by
  have hnn : ∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ (Pi.single l t : Fin N → ℝ) i := fun t ht i => by
    by_cases h : i = l
    · subst h; simp [ht]
    · simp [Pi.single_eq_of_ne h]
  have hms : MeasurableSet {r : Fin N → ℝ | r l ≤ 0} :=
    measurableSet_le (measurable_pi_apply l) measurable_const
  -- dominated convergence as `t → ∞`
  have hlim : Tendsto (fun t : ℝ => ∫ r, lap (Pi.single l t) r ∂νD) atTop
      (𝓝 (∫ r, {r : Fin N → ℝ | r l ≤ 0}.indicator 1 r ∂νD)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Eventually.of_forall fun t => (continuous_lap _).aestronglyMeasurable)
      (eventually_atTop.2 ⟨0, fun t ht => Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_of_pos (lap_pos _ r)]; exact lap_le_one (hnn t ht) r⟩)
      (integrable_const _) (Eventually.of_forall fun r => ?_)
    simp only [lap_single]
    by_cases hr : r l ≤ 0
    · rw [Set.indicator_of_mem (show r ∈ {r : Fin N → ℝ | r l ≤ 0} from hr), max_eq_right hr]
      simp
    · rw [Set.indicator_of_notMem (show r ∉ {r : Fin N → ℝ | r l ≤ 0} from hr),
        max_eq_left (le_of_lt (not_le.1 hr))]
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_mul_const (not_le.1 hr))
  have hval : Tendsto (fun t : ℝ => ∫ r, lap (Pi.single l t) r ∂νD) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_limL_single hL0 l)
    rw [ENNReal.toReal_zero] at h
    refine h.congr' (eventually_atTop.2 ⟨0, fun t ht => ?_⟩)
    show _ = ∫ r, lap (Pi.single l t) r ∂νD
    rw [Function.comp_apply, integral_lap_eq (nuD_supp hWk), nuD_ex hWk hBD hL0 (hnn t ht)]
  have e := tendsto_nhds_unique hlim hval
  rw [integral_indicator_one hms] at e
  refine measure_mono_null (fun r (hr : r l = 0) => (le_of_eq hr : r l ≤ 0)) ?_
  exact (measureReal_eq_zero_iff).1 e

/-- The exponents of the homogeneity argument. -/
def lpE (c : ℝ) (j : Fin N → ℕ) : Fin N → ℝ := fun l => ((j l : ℝ) + (c + 1)) / c - 1
def mpE (c : ℝ) (j : Fin N → ℕ) : Fin N → ℝ := fun l => (j l : ℝ) + c
def gpE (c : ℝ) (j : Fin N → ℕ) : Fin N → ℝ := fun l => (j l : ℝ) + (c + 1)

lemma ex_mul (lam lam' : Fin N → ℝ) (r : Fin N → ℝ) : ex lam r * ex lam' r = ex (lam + lam') r := by
  rw [ex, ex, ex, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add]

lemma measurable_eN : Measurable fun r : Fin N → ℝ => ENNReal.ofReal (Real.exp (-∑ i, r i)) := by
  fun_prop

lemma measurable_eS : Measurable fun r : Fin N → ℝ => ENNReal.ofReal (Real.exp (∑ i, r i)) := by
  fun_prop

/-- The weight `e^{-Σr}` times `e^{Σr}` is one. -/
lemma withDensity_eN_eS (P : Measure (Fin N → ℝ)) :
    (P.withDensity fun r => ENNReal.ofReal (Real.exp (-∑ i, r i))).withDensity
      (fun r => ENNReal.ofReal (Real.exp (∑ i, r i))) = P := by
  rw [← withDensity_mul _ measurable_eN measurable_eS]
  convert withDensity_one (μ := P)
  funext r
  simp only [Pi.mul_apply, Pi.one_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    ENNReal.ofReal_one]

lemma withDensity_ex_cancel (a : ℝ) (P : Measure (Fin N → ℝ)) :
    (P.withDensity (ex fun _ => a)).withDensity
      (fun r => ENNReal.ofReal (Real.exp (a * ∑ i, r i))) = P := by
  rw [← withDensity_mul _ (measurable_ex _) (by fun_prop)]
  convert withDensity_one (μ := P)
  funext r
  simp only [Pi.mul_apply, Pi.one_apply, ex]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Finset.mul_sum, neg_add_cancel,
    Real.exp_zero, ENNReal.ofReal_one]

/-- **Homogeneity of `ρ_D`** (TeX 1829-1839), from the scaling of `ρ_{ε,D}` (item C) and the
weak limit, through integer Laplace transforms. -/
theorem rhoLim_hom
    (hWk : ∀ phi : (Fin N → ℝ) →ᵇ ℝ, Tendsto (fun ε => ∫ r, phi r ∂wickNu G Γ ε m D)
      (widthFilter N) (𝓝 (∫ r, phi r ∂νD)))
    {κ : ℝ≥0∞} (hκ : κ ≠ ∞) {c : ℝ} (hc : 0 < c)
    (hSD : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) → ∀ A : Set (Fin N → ℝ), MeasurableSet A →
      wickRho G Γ ε m D (c • A) = κ * wickRho G Γ (fun i => ε i / c ^ 2) m D A) :
    ∀ A : Set (Fin N → ℝ), MeasurableSet A → rhoLim νD (c • A) = κ * rhoLim νD A := by
  have hc0 : c ≠ 0 := hc.ne'
  have hsupp := nuD_supp hWk
  have hfm : Measurable fun r : Fin N → ℝ => c⁻¹ • r := measurable_const_smul _
  have hpre : ∀ A : Set (Fin N → ℝ), (fun r : Fin N → ℝ => c⁻¹ • r) ⁻¹' A = c • A :=
    fun A => Set.preimage_smul_inv₀ hc0 A
  have hmapε : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) →
      (wickRho G Γ ε m D).map (fun r => c⁻¹ • r) =
        κ • wickRho G Γ (fun i => ε i / c ^ 2) m D := fun ε hε => by
    ext A hA
    rw [Measure.map_apply hfm hA, hpre, hSD ε hε A hA, Measure.smul_apply, smul_eq_mul]
  have hlp : ∀ (j : Fin N → ℕ) (l : Fin N), 0 ≤ lpE c j l := fun j l => by
    simp only [lpE]
    rw [sub_nonneg, le_div_iff₀ hc]
    have := (Nat.cast_nonneg (j l) : (0 : ℝ) ≤ j l); linarith
  have hmp : ∀ (j : Fin N → ℕ) (l : Fin N), 0 ≤ mpE c j l := fun j l => by
    simp only [mpE]; have := (Nat.cast_nonneg (j l) : (0 : ℝ) ≤ j l); linarith
  -- pointwise exponent identities
  have P1 : ∀ (j : Fin N → ℕ) (r : Fin N → ℝ), ENNReal.ofReal (Real.exp (-∑ i, r i)) * ex (lpE c j) r =
      ex (gpE c j) (c⁻¹ • r) := fun j r => by
    rw [ex_mul_ex, ex]
    congr 2
    have h : ∀ i, -(r i) - lpE c j i * r i = -(gpE c j i * (c⁻¹ • r) i) := fun i => by
      simp only [lpE, gpE, Pi.smul_apply, smul_eq_mul]; field_simp; ring
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => h i
  have P2 : ∀ (j : Fin N → ℕ) (r : Fin N → ℝ), ENNReal.ofReal (Real.exp (-∑ i, r i)) * ex (mpE c j) r =
      ex (gpE c j) r := fun j r => by
    rw [ex_mul_ex, ex]
    congr 2
    have h : ∀ i, -(r i) - mpE c j i * r i = -(gpE c j i * r i) := fun i => by
      simp only [mpE, gpE]; ring
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => h i
  have P3 : ∀ (j : Fin N → ℕ) (r : Fin N → ℝ), ENNReal.ofReal (Real.exp (∑ i, r i)) *
      (ex (fun _ => c + 1) (c⁻¹ • r) * ex (fun l => (j l : ℝ)) (c⁻¹ • r)) = ex (lpE c j) r :=
    fun j r => by
    rw [ex_mul, ex_mul_ex, ex]
    congr 2
    have h : ∀ i, r i - ((fun _ : Fin N => c + 1) + fun l : Fin N => (j l : ℝ)) i * (c⁻¹ • r) i =
        -(lpE c j i * r i) := fun i => by
      simp only [lpE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => h i
  have P4 : ∀ (j : Fin N → ℕ) (r : Fin N → ℝ), ENNReal.ofReal (Real.exp (∑ i, r i)) *
      (ex (fun _ => c + 1) r * ex (fun l => (j l : ℝ)) r) = ex (mpE c j) r := fun j r => by
    rw [ex_mul, ex_mul_ex, ex]
    congr 2
    have h : ∀ i, r i - ((fun _ : Fin N => c + 1) + fun l : Fin N => (j l : ℝ)) i * r i = -(mpE c j i * r i) :=
      fun i => by simp only [mpE, Pi.add_apply]; ring
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => h i
  -- the relation at every positive width
  have hrel : ∀ j : Fin N → ℕ, ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) →
      ∫⁻ r, ex (lpE c j) r ∂wickNu G Γ ε m D =
        κ * ∫⁻ r, ex (mpE c j) r ∂wickNu G Γ (fun i => ε i / c ^ 2) m D := fun j ε hε => by
    rw [wickNu, lintegral_withDensity_eq_lintegral_mul _ measurable_eN (measurable_ex _), wickNu,
      lintegral_withDensity_eq_lintegral_mul _ measurable_eN (measurable_ex _)]
    simp only [Pi.mul_apply, P1, P2]
    rw [← lintegral_map (measurable_ex _) hfm, hmapε ε hε, lintegral_smul_measure, smul_eq_mul]
  -- the scaled widths tend to zero
  have hscale : Tendsto (fun ε : Fin N → ℝ => fun i => ε i / c ^ 2) (widthFilter N)
      (widthFilter N) := by
    show Tendsto _ _ (𝓝[posOrthant N] 0)
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((by fun_prop : Continuous fun ε : Fin N → ℝ => fun i => ε i / c ^ 2).tendsto' 0 0
        (by funext i; simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_pos N] with ε hε
      simp only [posOrthant, Set.mem_univ_pi, mem_Ioi]
      exact fun i => div_pos (hε i) (pow_pos hc 2)
  have hfinD : ∀ lam : Fin N → ℝ, (∀ l, 0 ≤ lam l) → ∫⁻ r, ex lam r ∂νD ≠ ∞ := fun lam hlam =>
    ne_top_of_le_ne_top (measure_ne_top νD univ) (lintegral_ex_le hsupp hlam)
  -- the relation for the limit
  have hDrel : ∀ j : Fin N → ℕ, ∫⁻ r, ex (lpE c j) r ∂νD = κ * ∫⁻ r, ex (mpE c j) r ∂νD := fun j => by
    have t1 := tendsto_ex hWk (hlp j)
    have t3 := ((tendsto_ex hWk (hmp j)).comp hscale).const_mul κ.toReal
    have e := tendsto_nhds_unique t1 (t3.congr' (by
      filter_upwards [eventually_pos N] with ε hε
      rw [Function.comp_apply, hrel j ε hε, ENNReal.toReal_mul]))
    rw [← ENNReal.toReal_mul] at e
    exact (ENNReal.toReal_eq_toReal_iff' (hfinD _ (hlp j))
      (ENNReal.mul_ne_top hκ (hfinD _ (hmp j)))).1 e
  -- the weighted measures
  set Q1 := ((rhoLim νD).map fun r => c⁻¹ • r).withDensity (ex fun _ => c + 1) with hQ1
  set Q2 := (κ • rhoLim νD).withDensity (ex fun _ => c + 1) with hQ2
  have lint1 : ∀ j : Fin N → ℕ, ∫⁻ r, ex (fun l => (j l : ℝ)) r ∂Q1 = ∫⁻ r, ex (lpE c j) r ∂νD :=
    fun j => by
    have hm3 : Measurable fun r : Fin N → ℝ =>
        (((ex fun _ => c + 1) * ex fun l => (j l : ℝ)) : (Fin N → ℝ) → ℝ≥0∞) (c⁻¹ • r) :=
      ((measurable_ex _).mul (measurable_ex _)).comp hfm
    rw [hQ1, lintegral_withDensity_eq_lintegral_mul _ (measurable_ex _) (measurable_ex _),
      lintegral_map ((measurable_ex _).mul (measurable_ex _)) hfm, rhoLim,
      lintegral_withDensity_eq_lintegral_mul _ measurable_eS hm3]
    simp only [Pi.mul_apply, P3]
  have lint2 : ∀ j : Fin N → ℕ, ∫⁻ r, ex (fun l => (j l : ℝ)) r ∂Q2 =
      κ * ∫⁻ r, ex (mpE c j) r ∂νD := fun j => by
    rw [hQ2, withDensity_smul_measure, lintegral_smul_measure,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_ex _) (measurable_ex _), rhoLim,
      lintegral_withDensity_eq_lintegral_mul _ measurable_eS
        ((measurable_ex _).mul (measurable_ex _))]
    simp only [Pi.mul_apply, P4, smul_eq_mul]
  have hex0 : ∀ r : Fin N → ℝ, ex (fun l => (((0 : Fin N → ℕ) l : ℕ) : ℝ)) r = 1 := fun r => by
    simp [ex]
  have hQ1u : Q1 univ = ∫⁻ r, ex (lpE c 0) r ∂νD := by
    rw [← lint1 0, ← lintegral_one]; exact lintegral_congr fun r => (hex0 r).symm
  have hQ2u : Q2 univ = κ * ∫⁻ r, ex (mpE c 0) r ∂νD := by
    rw [← lint2 0, ← lintegral_one]; exact lintegral_congr fun r => (hex0 r).symm
  have : IsFiniteMeasure Q1 := ⟨by rw [hQ1u]; exact (hfinD _ (hlp 0)).lt_top⟩
  have : IsFiniteMeasure Q2 :=
    ⟨by rw [hQ2u]; exact (ENNReal.mul_ne_top hκ (hfinD _ (hmp 0))).lt_top⟩
  have hρs : rhoLim νD (nonneg N)ᶜ = 0 := (rhoLim_eq_zero_iff _ _).2 hsupp
  have hs1 : Q1 (nonneg N)ᶜ = 0 := by
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.map_apply hfm (measurableSet_nonneg N).compl]
    convert hρs using 2
    ext r
    simp only [mem_preimage, mem_compl_iff, mem_nonneg, Pi.smul_apply, smul_eq_mul]
    exact not_congr (forall_congr' fun l => mul_nonneg_iff_of_pos_left (inv_pos.2 hc))
  have hs2 : Q2 (nonneg N)ᶜ = 0 := by
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.smul_apply, hρs, smul_zero]
  have hQ : Q1 = Q2 := ext_of_laplace hs1 hs2 fun j => by
    rw [integral_lap_eq hs1, integral_lap_eq hs2, lint1, lint2, hDrel]
  have hmapM : (rhoLim νD).map (fun r => c⁻¹ • r) = κ • rhoLim νD := by
    rw [← withDensity_ex_cancel (c + 1) ((rhoLim νD).map fun r => c⁻¹ • r),
      ← withDensity_ex_cancel (c + 1) (κ • rhoLim νD)]
    exact congrArg (fun P : Measure (Fin N → ℝ) => P.withDensity
      (fun r => ENNReal.ofReal (Real.exp ((c + 1) * ∑ i, r i)))) hQ
  intro A hA
  rw [← hpre A, ← Measure.map_apply hfm hA, hmapM, Measure.smul_apply, smul_eq_mul]

/-- **`E:spatial-wick-limit`** (TeX 1689-1693, 1843-1847). -/
theorem tendsto_horizon
    (hfin : ∀ ε : Fin N → ℝ, (∀ i, 0 < ε i) → IsFiniteMeasure (wickNu G Γ ε m D))
    (hWk : ∀ phi : (Fin N → ℝ) →ᵇ ℝ, Tendsto (fun ε => ∫ r, phi r ∂wickNu G Γ ε m D)
      (widthFilter N) (𝓝 (∫ r, phi r ∂νD)))
    {T1 T2 : ℝ} (h1 : νD {r | ell1 m r = T1} = 0) (h2 : νD {r | ell2 m r = T2} = 0)
    (phi : (Fin N → ℝ) →ᵇ ℝ) :
    Tendsto (fun ε => ∫ r in horizon m T1 T2, phi r ∂wickRho G Γ ε m D) (widthFilter N)
      (𝓝 (∫ r in horizon m T1 T2, phi r ∂rhoLim νD)) := by
  have hHo : IsOpen (horizon m T1 T2 : Set (Fin N → ℝ)) :=
    (isOpen_lt (continuous_ell1 m) continuous_const).inter
      (isOpen_lt (continuous_ell2 m) continuous_const)
  have hHm := hHo.measurableSet
  set Φ : (Fin N → ℝ) → ℝ := (horizon m T1 T2).indicator fun r => Real.exp (∑ i, r i) * phi r
    with hΦ
  have hconv : ∀ P : Measure (Fin N → ℝ), ∫ r in horizon m T1 T2, phi r
      ∂(P.withDensity fun r => ENNReal.ofReal (Real.exp (∑ i, r i))) = ∫ r, Φ r ∂P := fun P => by
    have e : (fun r : Fin N → ℝ => ENNReal.ofReal (Real.exp (∑ i, r i))) =
        fun r => (((Real.exp (∑ i, r i)).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
    rw [e, setIntegral_withDensity_eq_setIntegral_smul (by fun_prop) _ hHm, hΦ,
      integral_indicator hHm]
    refine setIntegral_congr_fun hHm fun r _ => ?_
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, smul_eq_mul]
  have hrho : ∀ ε, wickRho G Γ ε m D =
      (wickNu G Γ ε m D).withDensity fun r => ENNReal.ofReal (Real.exp (∑ i, r i)) := fun ε =>
    (withDensity_eN_eS _).symm
  have hsum : ∀ r : Fin N → ℝ, r ∈ horizon m T1 T2 → ∑ i, r i < T1 + T2 := fun r hr => by
    rw [sum_eq_ell m r]; exact add_lt_add hr.1 hr.2
  have hΦC : ∀ r : Fin N → ℝ, |Φ r| ≤ Real.exp (T1 + T2) * ‖phi‖ := fun r => by
    by_cases hr : r ∈ horizon m T1 T2
    · rw [hΦ, Set.indicator_of_mem hr, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.2 (hsum r hr).le)
        (by rw [← Real.norm_eq_abs]; exact phi.norm_coe_le_norm r) (abs_nonneg _)
        (Real.exp_pos _).le
    · rw [hΦ, Set.indicator_of_notMem hr, abs_zero]; positivity
  have hcf : Continuous fun r : Fin N → ℝ => Real.exp (∑ i, r i) * phi r :=
    (by fun_prop : Continuous fun r : Fin N → ℝ => Real.exp (∑ i, r i)).mul phi.continuous
  have hlim := tendsto_integral_of_null (tendsto_finFam hfin hWk)
    (g := fun r => |ell1 m r - T1| * |ell2 m r - T2|)
    (by have := continuous_ell1 (N := N) m; have := continuous_ell2 (N := N) m; fun_prop)
    (fun r => by positivity)
    (by
      refine measure_mono_null (fun r hr => ?_) (measure_union_null h1 h2)
      simp only [Set.mem_ofPred_eq, mul_eq_zero, abs_eq_zero, sub_eq_zero] at hr
      exact hr)
    (hcf.measurable.indicator hHm) hΦC
    (fun y hy => by
      have hy1 : ell1 m y ≠ T1 := fun e => hy (by simp [e])
      have hy2 : ell2 m y ≠ T2 := fun e => hy (by simp [e])
      by_cases hyH : y ∈ horizon m T1 T2
      · refine hcf.continuousAt.congr ?_
        filter_upwards [hHo.mem_nhds hyH] with z hz
        simp only [Set.indicator_of_mem hz]
      · have hU : IsOpen {r : Fin N → ℝ | T1 < ell1 m r ∨ T2 < ell2 m r} :=
          (isOpen_lt continuous_const (continuous_ell1 m)).union
            (isOpen_lt continuous_const (continuous_ell2 m))
        have hyU : T1 < ell1 m y ∨ T2 < ell2 m y := by
          by_contra hc
          simp only [not_or, not_lt] at hc
          exact hyH ⟨lt_of_le_of_ne hc.1 hy1, lt_of_le_of_ne hc.2 hy2⟩
        refine (continuousAt_const (y := (0 : ℝ))).congr ?_
        filter_upwards [hU.mem_nhds hyU] with z hz
        refine (Set.indicator_of_notMem ?_ _).symm
        rintro ⟨hz1, hz2⟩
        rcases hz with hz | hz <;> linarith)
  rw [rhoLim, hconv]
  refine hlim.congr' ?_
  filter_upwards [eventually_pos N] with ε hε
  rw [finFam_of _ _ hfin hε, hrho ε, hconv]

end Weak

/-! ### The whole lemma -/

/-- **`L:spatial-wick-measures`, Step 5 from Step 4** (TeX lines 1679-1694 and 1824-1847 at
revision edf7085f, book 1.1.3): given the weak limit (Step 4 as the input `hW`, the target of
the unused fallback `SpatialWickWeakLimit`), `E:spatial-positive-laplace` (`hB`), the uniform mass bound
(`hC`) and the scaling of `ρ_{ε,D}` (`hS`), the limit has every property of the lemma. -/
theorem spatial_wick_measures_of_weak (d : ℕ) (hW : SpatialWickWeakLimitTarget d)
    (hB : SpatialPositiveLaplaceTarget d) (hC : WickMassBoundTarget d)
    (hS : RhoScalingTarget d) : SpatialWickMeasuresTarget d := by
  intro alpha α₀ Γ μ hH m n k hmn hk D hD
  obtain ⟨νD, hνfin, hfin, hWk⟩ := hW hH m n k hmn hk D hD
  obtain ⟨C, hCfin, hCb⟩ := hC hH m n k hmn hk D hD
  have hBD : ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) → ∀ lam : Fin (m + n) → ℝ, (∀ i, 0 ≤ lam i) →
      wickL (waveGreen d) Γ ε m D lam =
        ∫⁻ ξ, lapInt m D ε lam ξ ∂Measure.pi fun _ : openers D => μ :=
    fun ε hε lam hlam => hB hH m n k hmn hk D hD ε hε lam hlam
  have hL0 : limL μ m D 0 ≠ ∞ := ((limL_zero_le hBD hCb).trans_lt hCfin).ne
  have hom : ∀ c : ℝ, 0 < c → ∀ A : Set (Fin (m + n) → ℝ), MeasurableSet A →
      rhoLim νD (c • A) = ENNReal.ofReal (c ^ ((4 - alpha) * k)) * rhoLim νD A := fun c hc =>
    rhoLim_hom hWk ENNReal.ofReal_ne_top hc fun ε hε A hA => hS hH m n k hmn hk D hD ε hε c hc A hA
  have hκ : ∀ c : ℝ, 0 < c → ENNReal.ofReal (c ^ ((4 - alpha) * k)) ≠ 0 := fun c hc =>
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hc _)).ne'
  have hlev1 : ∀ T : ℝ, 0 < T → νD {r | ell1 m r = T} = 0 := fun T hT =>
    level_null νD (continuous_ell1 m) (ell1_smul m)
      (κ := fun c => ENNReal.ofReal (c ^ ((4 - alpha) * k))) hκ hom hT
  have hlev2 : ∀ T : ℝ, 0 < T → νD {r | ell2 m r = T} = 0 := fun T hT =>
    level_null νD (continuous_ell2 m) (ell2_smul m)
      (κ := fun c => ENNReal.ofReal (c ^ ((4 - alpha) * k))) hκ hom hT
  refine ⟨νD, hνfin, hfin, hWk, rhoLim_locallyFinite νD, hom,
    fun l => (rhoLim_eq_zero_iff _ _).2 (nuD_zero_face hWk hBD hL0 l),
    fun T hT => ⟨(rhoLim_eq_zero_iff _ _).2 (hlev1 T hT), (rhoLim_eq_zero_iff _ _).2 (hlev2 T hT)⟩,
    fun phi T1 T2 hT1 hT2 => tendsto_horizon hfin hWk (hlev1 T1 hT1) (hlev2 T2 hT2) phi⟩

/-- **`L:spatial-wick-measures`** (TeX lines 1679-1694, proof 1696-1848, at revision edf7085f,
book 1.1.3), the whole lemma from items B and C: `hB` (`E:spatial-positive-laplace`), `hC` (the
uniform mass bound) and `hS` (the scaling of `ρ_{ε,D}`).  Step 4 is `spatial_wick_weak_limit`;
the fallback named input `SpatialWickWeakLimit` is not used. -/
theorem spatial_wick_measures (d : ℕ) (hB : SpatialPositiveLaplaceTarget d)
    (hC : WickMassBoundTarget d) (hS : RhoScalingTarget d) : SpatialWickMeasuresTarget d :=
  spatial_wick_measures_of_weak d (spatial_wick_weak_limit d hB hC) hB hC hS

end StratonovichHAMSecondMoment.WickMeasures
