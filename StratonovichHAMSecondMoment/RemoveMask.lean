module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Proposition `P:variational-remove-mask` (Monotone rates and the original
point moment) of `notes/integrated_unmasked_variational.tex` at revision
a284420: statement TeX lines 168-179, proof lines 181-221, display
`E:variational-unmasked-point-lower` lines 175-178.  The section's standing
assumption (line 4) is a nonzero covariance satisfying `H:homog` with
`a = α₀`; the wrappers carry it as `HomogHypothesis.HomogCovariance`,
`Γ ≠ 0`, and use `a = α₀`.  Reused: the class `CPos`, the mean `h_{Ψ,s}`
(`mean`), `v_Ψ` in the integral form of `E:compact-raw-cost` (`rawCost`), the
rate `λ_{Ψ,s}` (`rate`, the square root of the real Rayleigh supremum of
`E:variational-real-rayleigh`) and `I_Ψ` (`integratedRate`) of
`VariationalDilation`; the Rayleigh sets of `WeakSobolev`; the dilation
floor of `VariationalFloor`; `VariationalMean.global_mean` and
`VariationalRate.unmasked_rate`.

New definitions: the profile `chi r = Real.smoothTransition (2 - r)`, which is
the TeX's `χ(r) = F(2-r)/(F(2-r) + F(r-1))` with `F(t) = e^{-1/t}` for
`t > 0` and `0` otherwise (`chi_eq`, `expNegInvGlue_eq`; lines 182-185); the
masks `mask R x = χ(|x|/R)`; the masked mean `m_R h_{Ψ,s}`
(`maskedMean`); the masked rate `λ_{R,s}` (`maskedRate`, the square root of
the supremum of the real Rayleigh values of `m_R h_s`, the convention of
`rate`); `∫_0^1 λ_{R,s} ds` (`maskedIntegratedRate`); the named input
`RawBlockOriginalLower`.

Formalized:
* The masks (lines 184-191, `mask_family`): `χ` has a positive denominator,
  is nonincreasing, smooth, `[0,1]`-valued, `1` on `r ≤ 1` and `0` on
  `r ≥ 2`; for `R > 0`, `m_R` is smooth (also at the origin), even, radial,
  `[0,1]`-valued, `1` on `|x| ≤ R`, supported in the closed ball of radius
  `2R`, nondecreasing in `R`, and `m_R → 1` pointwise.
* The rate clauses (lines 168-174, 193-212; general form `remove_mask`,
  wrapper `variational_remove_mask_rates_paper`, no supplied input): a common
  margin `ε > 0` for every `R ≥ R₀` (`ε ≤ λ_{R,s}² ≤ M`); monotonicity
  `λ_{R,s} ≤ λ_{R',s} ≤ λ_{Ψ,s}` for `0 < R ≤ R'`; the Lipschitz bound
  `C/(2√ε)` in `s` for `R ≥ R₀`; the exchange of the two suprema in the form
  `sup_{R ≥ R₀} sup R_{m_R h_s} = sup R_{h_s}`; pointwise convergence
  `λ_{R,s} → λ_{Ψ,s}`; uniform convergence on `I = [0,1]`; integrability,
  monotonicity and convergence `∫_I λ_{R,s} ds → I_Ψ`, each bounded by `I_Ψ`.
  The general exchange step is `tendsto_sSup_rayleighSet`: for potentials
  `V_i ≤ W`, `|V_i| ≤ B`, `V_i → W` pointwise, `sup R_{V_i} → sup R_W`.
* `E:variational-unmasked-point-lower` (lines 175-178, 214-218; general form
  `unmasked_point_lower`, wrapper `variational_remove_mask_paper`) over the
  named input: `2 I_Ψ - v_Ψ/2 ≤ liminf_{T→∞} L(T)` in `EReal`.

Supplied input (named, one): `RawBlockOriginalLower a Γ Ψ v L`, for all large
`R`, `2 ∫_0^1 λ_{R,s} ds - v/2 ≤ liminf_{T→∞} L(T)` in `EReal`, where `L(T)`
stands for `T^{-κ} log E|u(T,x)|²` at a fixed `x`.  It is
`E:raw-block-original-lower` (`P:raw-block-original-lower`,
`notes/integrated_raw_block_lower.tex` lines 541-549 at a284420) applied with
the mask `m_R`, which is eligible there (even, `[0,1]`-valued, one on `B_R`,
supported in the closed ball of radius `2R`, lines 7-8 of that file) for `R`
at least the radius of `P:compact-original-common-trial`, read with two
identifications the TeX makes: the compact ground rate of `m_R h_s` equals
the Rayleigh rate `maskedRate` (`integrated_unmasked_variational.tex`
lines 195-196, the argument of `E:variational-real-rayleigh`), and
`v_Ψ = E W(Ψ)²` equals the integral form
`rawCost` (`L:compact-raw-profile`).  It is no stronger than that source: it
is asserted only for all sufficiently large `R` (the source gives every
eligible `R`) and for one fixed `x`.  It is used only by the point-moment
display.

Narrower conclusions: the rates are the Rayleigh rates; the compact ground
statements (`P:compact-ground-family` for `m_R h_s`) and their identification
with the Rayleigh form are not formalized (foundation D8), as for `λ_{Ψ,s}`
in `VariationalRate`.  The canonical solution `u` and its second moment are
not defined in Lean; the point-moment display is the assembly step from the
named input, for the same `L`.

Implicit hypotheses made explicit: `I = [0,1]`; "uniformly on `I`" is
`TendstoUniformlyOn` on `Icc 0 1`; finiteness of the suprema is stated as
nonempty bounded-above value sets; integrability of `λ_{R,·}` on `(0,1)`
is part of the conclusion; the liminf is taken in `EReal`, so it is never a
junk value.  The TeX's masks have `R > 0`; for `R ≤ 0` the Lean definition
gives `m_R ≡ 1` (division convention at `R = 0`, sign for `R < 0`), and the
smoothness, plateau, support and monotonicity statements assume `R > 0`
(continuity, the `[0,1]` bounds, radiality and evenness hold for every `R`).

Proof routes that differ from the TeX:
* Common margin: the TeX uses the compact trial of
  `P:compact-original-common-trial` (line 193).  Here the trial is the test
  function of `VariationalFloor.dilation_floor` (the route of
  `VariationalRate.unmasked_rate`), supported in a ball of radius `R₁`;
  `R₀ = R₁ + 1`, and for `R ≥ R₀` its masked and unmasked Rayleigh values
  coincide.
* Exchange of suprema: proved as convergence of the suprema as `R → ∞`
  (dominated convergence for each fixed trial, lines 197-199), from which the
  supremum over `R ≥ R₀` follows by monotonicity.
* Uniform convergence: Mathlib's Dini theorem
  (`Monotone.tendstoUniformlyOn_of_forall_tendsto`) applied to the monotone
  family `R ↦ λ_{max(R,R₀),s}` of continuous functions on `I`, which equals
  `λ_{R,s}` for `R ≥ R₀`; the TeX runs the finite-subcover argument along
  `R_n = R₀ + n` and extends by monotonicity (lines 208-211).
* `∫_I λ_{R,s} ds → I_Ψ`: dominated convergence with the bound `√M`; the TeX
  deduces it from the uniform convergence (line 212).
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.WeakSobolev
public import StratonovichHAMSecondMoment.VariationalDilation
public import StratonovichHAMSecondMoment.VariationalMean
public import StratonovichHAMSecondMoment.VariationalFloor
public import StratonovichHAMSecondMoment.VariationalRate

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace StratonovichHAMSecondMoment.RemoveMask

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open WeakSobolev
open VariationalDilation (CPos SetScaling mean rawCost rate integratedRate)
open VariationalMean (global_mean integrable_pot_of_bounded mean_continuous_of_lip)
open VariationalFloor (dilation_floor exists_radius_fn fl gl fl_test fl_unit gl_memLp gl_weak
  memLp_test)
open VariationalRate (psiBar psiBar_data psiBar_conv_integrable conv_psiBar_le_mean unmasked_rate
  abs_sSup_rayleighSet_sub_le rayleighValue_le abs_sqrt_sub_le alpha_lt_two)

variable {d : ℕ}

/-! ### The profile `χ` and the masks `m_R` -/

/-- The TeX's `F` (line 182): `F(t) = e^{-1/t}` for `t > 0` and `0` otherwise
is Mathlib's `expNegInvGlue`. -/
theorem expNegInvGlue_eq (t : ℝ) :
    expNegInvGlue t = if t ≤ 0 then 0 else Real.exp (-(1 / t)) := by
  rw [one_div]; rfl

/-- The profile of the masks (TeX line 184), `χ(r) = smoothTransition(2 - r)`. -/
def chi (r : ℝ) : ℝ := Real.smoothTransition (2 - r)

/-- `χ` is the TeX's quotient: `χ(r) = F(2-r)/(F(2-r) + F(r-1))` (line 184). -/
theorem chi_eq (r : ℝ) :
    chi r = expNegInvGlue (2 - r) / (expNegInvGlue (2 - r) + expNegInvGlue (r - 1)) := by
  unfold chi Real.smoothTransition
  rw [show (1 : ℝ) - (2 - r) = r - 1 by ring]

/-- The denominator of `χ` is positive (line 187). -/
theorem chi_denom_pos (r : ℝ) : 0 < expNegInvGlue (2 - r) + expNegInvGlue (r - 1) := by
  have := Real.smoothTransition.pos_denom (2 - r)
  rwa [show (1 : ℝ) - (2 - r) = r - 1 by ring] at this

/-- `χ` is nonincreasing (lines 187-188). -/
theorem chi_antitone : Antitone chi := fun _ _ hab =>
  Real.smoothTransition.monotone (by linarith)

/-- `χ = 1` on `r ≤ 1` (line 188). -/
theorem chi_eq_one {r : ℝ} (hr : r ≤ 1) : chi r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- `χ = 0` on `r ≥ 2` (line 189). -/
theorem chi_eq_zero {r : ℝ} (hr : 2 ≤ r) : chi r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- `0 ≤ χ ≤ 1` (line 191). -/
theorem chi_mem (r : ℝ) : 0 ≤ chi r ∧ chi r ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- `χ` is smooth (line 189). -/
theorem chi_contDiff : ContDiff ℝ ∞ chi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

/-- Auxiliary to the Lean proof route: `χ` is continuous. -/
theorem chi_continuous : Continuous chi :=
  Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id)

/-- The masks of the TeX (line 185): `m_R(x) = χ(|x|/R)`.  (For `R = 0`
Lean's division convention, and for `R < 0` the sign, make `m_R ≡ 1`; the
smoothness, plateau, support and monotonicity statements below assume
`R > 0`, the limits concern `R → ∞`.) -/
def mask (R : ℝ) (x : Rd d) : ℝ := chi (‖x‖ / R)

/-- Auxiliary to the Lean proof route: `m_R` is continuous (every `R`). -/
theorem mask_continuous (R : ℝ) : Continuous (mask (d := d) R) :=
  chi_continuous.comp (continuous_norm.div_const R)

/-- `0 ≤ m_R ≤ 1` (line 191). -/
theorem mask_mem (R : ℝ) (x : Rd d) : 0 ≤ mask R x ∧ mask R x ≤ 1 := chi_mem _

/-- `m_R` is radial (line 170). -/
theorem mask_radial (R : ℝ) {x y : Rd d} (h : ‖x‖ = ‖y‖) : mask R x = mask R y := by
  simp only [mask, h]

/-- `m_R` is even (line 191). -/
theorem mask_neg (R : ℝ) (x : Rd d) : mask R (-x) = mask R x := by
  simp only [mask, norm_neg]

/-- `m_R = 1` on the closed ball `|x| ≤ R` (from line 188). -/
theorem mask_eq_one {R : ℝ} (hR : 0 < R) {x : Rd d} (hx : ‖x‖ ≤ R) : mask R x = 1 :=
  chi_eq_one ((div_le_one hR).2 hx)

/-- `m_R = 0` on `|x| ≥ 2R` (from line 189). -/
theorem mask_eq_zero {R : ℝ} (hR : 0 < R) {x : Rd d} (hx : 2 * R ≤ ‖x‖) : mask R x = 0 :=
  chi_eq_zero ((le_div_iff₀ hR).2 hx)

/-- The support of `m_R` lies in the closed ball of radius `2R` (from line
189). -/
theorem tsupport_mask_subset {R : ℝ} (hR : 0 < R) :
    tsupport (mask (d := d) R) ⊆ closedBall 0 (2 * R) := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  by_contra h
  rw [mem_closedBall, dist_zero_right, not_le] at h
  exact hx (mask_eq_zero hR h.le)

/-- Auxiliary to the Lean proof route: `m_R` has compact support. -/
theorem mask_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (mask (d := d) R) :=
  (isCompact_closedBall 0 (2 * R)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_mask_subset hR)

/-- `m_R` is smooth for `R > 0`, also at the origin, where it is constant
(lines 189-190). -/
theorem mask_contDiff {R : ℝ} (hR : 0 < R) : ContDiff ℝ ∞ (mask (d := d) R) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · have : (mask (d := d) R) =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [ball_mem_nhds x hR] with y hy
      rw [hx, mem_ball, dist_zero_right] at hy
      exact mask_eq_one hR hy.le
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact chi_contDiff.contDiffAt.comp x ((contDiffAt_norm ℝ hx).div_const R)

/-- The masks increase in `R > 0` (line 191). -/
theorem mask_mono {R R' : ℝ} (hR : 0 < R) (hRR : R ≤ R') (x : Rd d) :
    mask R x ≤ mask R' x :=
  chi_antitone (div_le_div_of_nonneg_left (norm_nonneg x) hR hRR)

/-- Auxiliary to the Lean proof route: at every point, `m_R = 1` for all
large `R`. -/
theorem mask_eventually_one (x : Rd d) : ∀ᶠ R in atTop, mask R x = 1 := by
  filter_upwards [eventually_ge_atTop (max ‖x‖ 1)] with R hR
  exact mask_eq_one (lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR))
    ((le_max_left _ _).trans hR)

/-- The masks tend to one pointwise (line 191). -/
theorem mask_tendsto (x : Rd d) : Tendsto (fun R => mask R x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((mask_eventually_one x).mono fun _ h => h.symm)

/-! ### Rayleigh value sets: comparison and the exchange of suprema -/

/-- Auxiliary to the Lean proof route: the Rayleigh value set of a potential
with `V f²` integrable for every `f ∈ L²` is nonempty (the unit test
`VariationalFloor.fl 1` is a trial). -/
theorem rayleighSet_nonempty {V : Rd d → ℝ}
    (hV : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => V x * f x ^ 2) volume) :
    (rayleighSet V).Nonempty :=
  ⟨_, fl 1, gl 1, ⟨memLp_test (fl_test one_pos), gl_memLp one_pos, gl_weak one_pos,
    fl_unit one_pos, hV _ (memLp_test (fl_test one_pos))⟩, rfl⟩

/-- Auxiliary to the Lean proof route.  Comparison of Rayleigh values: if `V ≤ W` pointwise, `W f²` is integrable
for every `f ∈ L²` and the value set of `W` is bounded above, then every
Rayleigh value of `V` is at most `sup R_W`. -/
theorem rayleighValue_le_sSup_of_le {V W : Rd d → ℝ} (hVW : ∀ x, V x ≤ W x)
    (hW : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => W x * f x ^ 2) volume)
    (hbW : BddAbove (rayleighSet W)) {q : ℝ} (hq : q ∈ rayleighSet V) :
    q ≤ sSup (rayleighSet W) := by
  obtain ⟨f, g, hT, rfl⟩ := hq
  have hTW : IsRayleighTrial W f g :=
    ⟨hT.memLp_f, hT.memLp_g, hT.weakGrad, hT.unit, hW f hT.memLp_f⟩
  refine le_trans ?_ (le_csSup hbW ⟨f, g, hTW, rfl⟩)
  unfold rayleighValue
  have : ∫ x, V x * f x ^ 2 ≤ ∫ x, W x * f x ^ 2 :=
    integral_mono hT.integrable_pot hTW.integrable_pot
      fun x => mul_le_mul_of_nonneg_right (hVW x) (sq_nonneg _)
  linarith

/-- Auxiliary to the Lean proof route.  Monotonicity of the Rayleigh
supremum in the potential: if `V ≤ W`
pointwise, both `V f²` and `W f²` are integrable for every `f ∈ L²`, and the
value set of `W` is bounded above, then the value set of `V` is nonempty and
bounded above and `sup R_V ≤ sup R_W`. -/
theorem sSup_rayleighSet_mono {V W : Rd d → ℝ} (hVW : ∀ x, V x ≤ W x)
    (hV : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => V x * f x ^ 2) volume)
    (hW : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => W x * f x ^ 2) volume)
    (hbW : BddAbove (rayleighSet W)) :
    (rayleighSet V).Nonempty ∧ BddAbove (rayleighSet V) ∧
      sSup (rayleighSet V) ≤ sSup (rayleighSet W) :=
  ⟨rayleighSet_nonempty hV, ⟨_, fun _ hq => rayleighValue_le_sSup_of_le hVW hW hbW hq⟩,
    csSup_le (rayleighSet_nonempty hV) fun _ hq => rayleighValue_le_sSup_of_le hVW hW hbW hq⟩

/-- The exchange of the two suprema (TeX lines 197-207) for a general family
of potentials.  Let `V_i ≤ W` pointwise, `|V_i| ≤ B`, `V_i → W` pointwise
along a countably generated filter, with `V_i f²` and `W f²` integrable for
every `f ∈ L²`, and the value set of `W` nonempty and bounded above.  Then
`sup R_{V_i} → sup R_W`.  (For each fixed unit `f`, dominated convergence
gives `∫ V_i f² → ∫ W f²`.) -/
theorem tendsto_sSup_rayleighSet {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {V : ι → Rd d → ℝ} {W : Rd d → ℝ} {B : ℝ}
    (hV : ∀ i, ∀ f : Rd d → ℝ, MemLp f 2 volume →
      Integrable (fun x => V i x * f x ^ 2) volume)
    (hW : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => W x * f x ^ 2) volume)
    (hle : ∀ i x, V i x ≤ W x) (hB : ∀ i x, |V i x| ≤ B)
    (hlim : ∀ x, Tendsto (fun i => V i x) l (𝓝 (W x)))
    (hneW : (rayleighSet W).Nonempty) (hbW : BddAbove (rayleighSet W)) :
    Tendsto (fun i => sSup (rayleighSet (V i))) l (𝓝 (sSup (rayleighSet W))) := by
  have hmono := fun i => sSup_rayleighSet_mono (hle i) (hV i) hW hbW
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨q, ⟨f, g, hT, rfl⟩, hbq⟩ := exists_lt_of_lt_csSup hneW hb
    have hf := hT.memLp_f
    have hDCT : Tendsto (fun i => ∫ x, V i x * f x ^ 2) l (𝓝 (∫ x, W x * f x ^ 2)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => B * f x ^ 2)
        (Eventually.of_forall fun i => (hV i f hf).aestronglyMeasurable)
        (Eventually.of_forall fun i => ae_of_all _ fun x => ?_)
        (hf.integrable_sq.const_mul B) (ae_of_all _ fun x => (hlim x).mul_const _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (f x))]
      exact mul_le_mul_of_nonneg_right (hB i x) (sq_nonneg _)
    have hval : Tendsto (fun i => rayleighValue (V i) f g) l (𝓝 (rayleighValue W f g)) :=
      hDCT.sub_const _
    filter_upwards [hval.eventually (lt_mem_nhds hbq)] with i hi
    have hTi : IsRayleighTrial (V i) f g :=
      ⟨hT.memLp_f, hT.memLp_g, hT.weakGrad, hT.unit, hV i f hf⟩
    exact lt_of_lt_of_le hi (le_csSup (hmono i).2.1 ⟨f, g, hTi, rfl⟩)
  · exact Eventually.of_forall fun i => lt_of_le_of_lt (hmono i).2.2 hb

/-! ### The masked means and rates -/

/-- The masked mean `m_R h_{Ψ,s}`. -/
def maskedMean (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) (R s : ℝ) (x : Rd d) : ℝ :=
  mask R x * mean a Γ Ψ s x

/-- The masked rate `λ_{R,s} = √(sup of the real Rayleigh values of m_R h_s)`
(the Rayleigh convention of `VariationalDilation.rate`). -/
def maskedRate (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) (R s : ℝ) : ℝ :=
  rayleighRate (maskedMean a Γ Ψ R s)

/-- `∫_0^1 λ_{R,s} ds`. -/
def maskedIntegratedRate (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) (R : ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) 1, maskedRate a Γ Ψ R s

/-- **`P:variational-remove-mask`, rate part, general form** (TeX lines
168-174 and 193-212).  For tempered `Γ`, `μ` with the spectral convention,
`Γ` nonzero and locally finite with the set scaling of `H:homog`, `α < 2`,
`0 ≤ a < 1` and `Ψ ∈ CPos`: there are reals `ε > 0`, `M ≥ ε`, `C ≥ 0`,
`R₀ > 0` such that (i) for `R ≥ R₀` and `s ∈ [0,1]` the Rayleigh value set
of `m_R h_s` is nonempty and bounded above, `ε ≤ λ_{R,s}² = sup ≤ M` and
`√ε ≤ λ_{R,s} ≤ √M`; (ii) for `s ∈ [0,1]` and `0 < R ≤ R'`,
`λ_{R,s} ≤ λ_{R',s} ≤ λ_{Ψ,s}`; (iii) for `R ≥ R₀`,
`|λ_{R,s} - λ_{R,t}| ≤ C/(2√ε) |s - t|` on `[0,1]`; (iv) for `s ∈ [0,1]`,
the supremum over `R ≥ R₀` of the suprema of the value sets of `m_R h_s` is
the supremum of the value set of `h_s`; (v) `λ_{R,s} → λ_{Ψ,s}` as
`R → ∞` for `s ∈ [0,1]`; (vi) uniformly on `[0,1]`; (vii) for `R ≥ R₀`,
`λ_{R,·}` is integrable on `(0,1)`, `∫_0^1 λ_{R,s} ds` is nondecreasing in
`R ≥ R₀` and at most `I_Ψ`, and it tends to `I_Ψ`.  Route differences: see
the module doc. -/
theorem remove_mask {alpha : ℝ} {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hα : alpha < 2) (hΓ : Γ ≠ 0) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    ∃ ε M C R₀ : ℝ, 0 < ε ∧ ε ≤ M ∧ 0 ≤ C ∧ 0 < R₀ ∧
      (∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1,
        (rayleighSet (maskedMean a Γ Ψ R s)).Nonempty ∧
        BddAbove (rayleighSet (maskedMean a Γ Ψ R s)) ∧
        ε ≤ sSup (rayleighSet (maskedMean a Γ Ψ R s)) ∧
        sSup (rayleighSet (maskedMean a Γ Ψ R s)) ≤ M ∧
        maskedRate a Γ Ψ R s ^ 2 = sSup (rayleighSet (maskedMean a Γ Ψ R s)) ∧
        Real.sqrt ε ≤ maskedRate a Γ Ψ R s ∧ maskedRate a Γ Ψ R s ≤ Real.sqrt M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ R R', 0 < R → R ≤ R' →
        maskedRate a Γ Ψ R s ≤ maskedRate a Γ Ψ R' s ∧
        maskedRate a Γ Ψ R' s ≤ rate a Γ Ψ s) ∧
      (∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |maskedRate a Γ Ψ R s - maskedRate a Γ Ψ R t| ≤
          C / (2 * Real.sqrt ε) * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        sSup ((fun R => sSup (rayleighSet (maskedMean a Γ Ψ R s))) '' Ici R₀) =
          sSup (rayleighSet (mean a Γ Ψ s))) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        Tendsto (fun R => maskedRate a Γ Ψ R s) atTop (𝓝 (rate a Γ Ψ s))) ∧
      TendstoUniformlyOn (fun R s => maskedRate a Γ Ψ R s) (rate a Γ Ψ) atTop (Icc 0 1) ∧
      (∀ R, R₀ ≤ R → IntegrableOn (maskedRate a Γ Ψ R) (Ioo 0 1)) ∧
      (∀ R R', R₀ ≤ R → R ≤ R' →
        maskedIntegratedRate a Γ Ψ R ≤ maskedIntegratedRate a Γ Ψ R' ∧
        maskedIntegratedRate a Γ Ψ R' ≤ integratedRate a Γ Ψ) ∧
      Tendsto (maskedIntegratedRate a Γ Ψ) atTop (𝓝 (integratedRate a Γ Ψ)) := by
  -- the unmasked rate and the mean
  obtain ⟨ε', M, C, -, -, hC, hbd, hlipx, hU, -, hUlip, hUint, -, -⟩ :=
    unmasked_rate hΓt hμt hsp hS hα hΓ ha0 ha hΨ
  obtain ⟨M₀, C₀, -, hC₀, -, -, -, hlip0⟩ := global_mean hΓt hμt hsp hΨ ha
  have hcont : ∀ s ∈ Icc (0 : ℝ) 1, Continuous (mean a Γ Ψ s) := fun s hs =>
    mean_continuous_of_lip hC₀ fun x x' => hlip0 s hs s hs x x'
  have hmcont : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, Continuous (maskedMean a Γ Ψ R s) := fun R s hs =>
    (mask_continuous R).mul (hcont s hs)
  have hmbd : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x,
      0 ≤ maskedMean a Γ Ψ R s x ∧ maskedMean a Γ Ψ R s x ≤ mean a Γ Ψ s x ∧
        |maskedMean a Γ Ψ R s x| ≤ M := by
    intro R s hs x
    obtain ⟨h0, h1⟩ := mask_mem R x
    obtain ⟨hm0, hmM⟩ := hbd s hs x
    have hle : maskedMean a Γ Ψ R s x ≤ mean a Γ Ψ s x := by
      unfold maskedMean; nlinarith
    have hnn : 0 ≤ maskedMean a Γ Ψ R s x := mul_nonneg h0 hm0
    exact ⟨hnn, hle, by rw [abs_of_nonneg hnn]; linarith⟩
  have hpot : ∀ s ∈ Icc (0 : ℝ) 1, ∀ f : Rd d → ℝ, MemLp f 2 volume →
      Integrable (fun x => mean a Γ Ψ s x * f x ^ 2) volume := fun s hs f hf =>
    integrable_pot_of_bounded (hcont s hs) (M := M) (fun x => by
      rw [abs_of_nonneg (hbd s hs x).1]; exact (hbd s hs x).2) hf
  have hmpot : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, ∀ f : Rd d → ℝ, MemLp f 2 volume →
      Integrable (fun x => maskedMean a Γ Ψ R s x * f x ^ 2) volume := fun R s hs f hf =>
    integrable_pot_of_bounded (hmcont R s hs) (fun x => (hmbd R s hs x).2.2) hf
  -- the common trial and its plateau radius
  obtain ⟨hzc, hz0, hzs, σ₀, x₀, -, -, hzpos⟩ := psiBar_data hΨ
  have hzne : psiBar Ψ ≠ 0 := fun h => by rw [h] at hzpos; exact lt_irrefl _ hzpos
  obtain ⟨f, g, ε, hε, hft, hf, hg, hw, hu, hval⟩ :=
    dilation_floor hS hα hΓ hzc hzs hz0 hzne (psiBar_conv_integrable hΓt hμt hsp hΨ)
  obtain ⟨R₁, hR₁0, hR₁⟩ := exists_radius_fn hft.2
  set R₀ : ℝ := R₁ + 1 with hR₀def
  have hR₀ : 0 < R₀ := by linarith
  have hsame : ∀ R, R₀ ≤ R → ∀ s, ∀ x,
      maskedMean a Γ Ψ R s x * f x ^ 2 = mean a Γ Ψ s x * f x ^ 2 := by
    intro R hR s x
    by_cases hx : ‖x‖ ≤ R₁
    · rw [maskedMean, mask_eq_one (by linarith) (by linarith), one_mul]
    · rw [hR₁ x (lt_of_not_ge hx)]; ring
  have hmT : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, IsRayleighTrial (maskedMean a Γ Ψ R s) f g :=
    fun R s hs => ⟨hf, hg, hw, hu, hmpot R s hs f hf⟩
  have hmne : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, (rayleighSet (maskedMean a Γ Ψ R s)).Nonempty :=
    fun R s hs => ⟨_, f, g, hmT R s hs, rfl⟩
  have hmbdd : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, BddAbove (rayleighSet (maskedMean a Γ Ψ R s)) :=
    fun R s hs => ⟨M, fun q hq => rayleighValue_le (fun x =>
      (le_abs_self _).trans (hmbd R s hs x).2.2) hq⟩
  have hmhi : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, sSup (rayleighSet (maskedMean a Γ Ψ R s)) ≤ M :=
    fun R s hs => csSup_le (hmne R s hs) fun q hq => rayleighValue_le (fun x =>
      (le_abs_self _).trans (hmbd R s hs x).2.2) hq
  have hmlo : ∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1,
      ε ≤ sSup (rayleighSet (maskedMean a Γ Ψ R s)) := by
    intro R hR s hs
    have hv : rayleighValue (maskedMean a Γ Ψ R s) f g = rayleighValue (mean a Γ Ψ s) f g := by
      unfold rayleighValue
      simp_rw [hsame R hR s]
    have hge : ε ≤ rayleighValue (mean a Γ Ψ s) f g :=
      hval _ (conv_psiBar_le_mean hΓt hμt hsp hΨ ha0 ha hs) (hpot s hs f hf)
    exact (hge.trans_eq hv.symm).trans (le_csSup (hmbdd R s hs) ⟨f, g, hmT R s hs, rfl⟩)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hεM : ε ≤ M := (hmlo R₀ le_rfl 0 h0).trans (hmhi R₀ 0 h0)
  have hmrate : ∀ R s, maskedRate a Γ Ψ R s =
      Real.sqrt (sSup (rayleighSet (maskedMean a Γ Ψ R s))) := fun _ _ => rfl
  have hrate : ∀ s, rate a Γ Ψ s = Real.sqrt (sSup (rayleighSet (mean a Γ Ψ s))) :=
    fun _ => rfl
  -- (i) floor and ceiling
  have hI : ∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1,
      (rayleighSet (maskedMean a Γ Ψ R s)).Nonempty ∧
      BddAbove (rayleighSet (maskedMean a Γ Ψ R s)) ∧
      ε ≤ sSup (rayleighSet (maskedMean a Γ Ψ R s)) ∧
      sSup (rayleighSet (maskedMean a Γ Ψ R s)) ≤ M ∧
      maskedRate a Γ Ψ R s ^ 2 = sSup (rayleighSet (maskedMean a Γ Ψ R s)) ∧
      Real.sqrt ε ≤ maskedRate a Γ Ψ R s ∧ maskedRate a Γ Ψ R s ≤ Real.sqrt M := by
    intro R hR s hs
    refine ⟨hmne R s hs, hmbdd R s hs, hmlo R hR s hs, hmhi R s hs, ?_, ?_, ?_⟩
    · rw [hmrate]; exact Real.sq_sqrt (hε.le.trans (hmlo R hR s hs))
    · rw [hmrate]; exact Real.sqrt_le_sqrt (hmlo R hR s hs)
    · rw [hmrate]; exact Real.sqrt_le_sqrt (hmhi R s hs)
  -- (ii) monotone in `R`, below the unmasked rate
  have hII : ∀ s ∈ Icc (0 : ℝ) 1, ∀ R R', 0 < R → R ≤ R' →
      maskedRate a Γ Ψ R s ≤ maskedRate a Γ Ψ R' s ∧
      maskedRate a Γ Ψ R' s ≤ rate a Γ Ψ s := by
    intro s hs R R' hR hRR
    have h1 := sSup_rayleighSet_mono (V := maskedMean a Γ Ψ R s) (W := maskedMean a Γ Ψ R' s)
      (fun x => mul_le_mul_of_nonneg_right (mask_mono hR hRR x) (hbd s hs x).1)
      (hmpot R s hs) (hmpot R' s hs) (hmbdd R' s hs)
    have h2 := sSup_rayleighSet_mono (V := maskedMean a Γ Ψ R' s) (W := mean a Γ Ψ s)
      (fun x => (hmbd R' s hs x).2.1) (hmpot R' s hs) (hpot s hs) (hU s hs).2.1
    exact ⟨Real.sqrt_le_sqrt h1.2.2, by rw [hrate]; exact Real.sqrt_le_sqrt h2.2.2⟩
  -- (iii) Lipschitz in `s`
  have hIII : ∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |maskedRate a Γ Ψ R s - maskedRate a Γ Ψ R t| ≤ C / (2 * Real.sqrt ε) * |s - t| := by
    intro R hR s hs t ht
    have hD : ∀ x, |maskedMean a Γ Ψ R s x - maskedMean a Γ Ψ R t x| ≤ C * |s - t| := by
      intro x
      rw [maskedMean, maskedMean, ← mul_sub, abs_mul, abs_of_nonneg (mask_mem R x).1]
      calc mask R x * |mean a Γ Ψ s x - mean a Γ Ψ t x|
          ≤ 1 * |mean a Γ Ψ s x - mean a Γ Ψ t x| :=
            mul_le_mul_of_nonneg_right (mask_mem R x).2 (abs_nonneg _)
        _ ≤ C * |s - t| := by rw [one_mul]; exact hlipx s hs t ht x
    have hsup := abs_sSup_rayleighSet_sub_le hD (hmpot R s hs) (hmpot R t ht) (hmne R s hs)
      (hmne R t ht) (hmbdd R s hs) (hmbdd R t ht)
    rw [hmrate, hmrate]
    refine (abs_sqrt_sub_le hε (hmlo R hR s hs) (hmlo R hR t ht)).trans ?_
    rw [div_mul_eq_mul_div, mul_comm C]
    exact div_le_div_of_nonneg_right (by rw [mul_comm]; exact hsup) (by positivity)
  -- (v) pointwise convergence of the squared rates and of the rates
  have hsupT : ∀ s ∈ Icc (0 : ℝ) 1, Tendsto (fun R => sSup (rayleighSet (maskedMean a Γ Ψ R s)))
      atTop (𝓝 (sSup (rayleighSet (mean a Γ Ψ s)))) := fun s hs =>
    tendsto_sSup_rayleighSet (fun R => hmpot R s hs) (hpot s hs) (fun R x => (hmbd R s hs x).2.1)
      (fun R x => (hmbd R s hs x).2.2) (fun x => by
        have := (mask_tendsto x).mul_const (mean a Γ Ψ s x)
        rwa [one_mul] at this) (hU s hs).1 (hU s hs).2.1
  have hV : ∀ s ∈ Icc (0 : ℝ) 1,
      Tendsto (fun R => maskedRate a Γ Ψ R s) atTop (𝓝 (rate a Γ Ψ s)) := fun s hs => by
    simp_rw [hmrate, hrate]
    exact (Real.continuous_sqrt.tendsto _).comp (hsupT s hs)
  -- (iv) the exchange of suprema over `R ≥ R₀`
  have hIV : ∀ s ∈ Icc (0 : ℝ) 1,
      sSup ((fun R => sSup (rayleighSet (maskedMean a Γ Ψ R s))) '' Ici R₀) =
        sSup (rayleighSet (mean a Γ Ψ s)) := by
    intro s hs
    refine IsLUB.csSup_eq ⟨?_, fun b hb => ?_⟩ ((nonempty_Ici).image _)
    · rintro _ ⟨R, -, rfl⟩
      exact (sSup_rayleighSet_mono (fun x => (hmbd R s hs x).2.1) (hmpot R s hs) (hpot s hs)
        (hU s hs).2.1).2.2
    · exact le_of_tendsto (hsupT s hs)
        ((eventually_ge_atTop R₀).mono fun R hR => hb ⟨R, hR, rfl⟩)
  -- (vi) uniform convergence (Dini)
  have hcontOn : ∀ R, R₀ ≤ R → ContinuousOn (maskedRate a Γ Ψ R) (Icc 0 1) := by
    intro R hR
    refine (LipschitzOnWith.of_dist_le_mul
      (K := Real.toNNReal (C / (2 * Real.sqrt ε))) fun s hs t ht => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact hIII R hR s hs t ht
  have hUcont : ContinuousOn (rate a Γ Ψ) (Icc 0 1) := by
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |rate a Γ Ψ s - rate a Γ Ψ t| ≤ K * |s - t| := ⟨_, hUlip⟩
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal K) fun s hs t ht => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq]
    exact (hK s hs t ht).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K)
      (abs_nonneg _))
  have hVI : TendstoUniformlyOn (fun R s => maskedRate a Γ Ψ R s) (rate a Γ Ψ) atTop
      (Icc 0 1) := by
    have hmax : Tendsto (fun R : ℝ => max R R₀) atTop atTop :=
      tendsto_atTop_mono (fun R => le_max_left R R₀) tendsto_id
    have hD : TendstoUniformlyOn (fun R s => maskedRate a Γ Ψ (max R R₀) s) (rate a Γ Ψ) atTop
        (Icc 0 1) :=
      Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
        (fun R => hcontOn _ (le_max_right _ _))
        (fun s hs R R' hRR => (hII s hs (max R R₀) (max R' R₀)
          (lt_of_lt_of_le hR₀ (le_max_right _ _)) (max_le_max hRR le_rfl)).1)
        hUcont (fun s hs => (hV s hs).comp hmax)
    refine hD.congr ((eventually_ge_atTop R₀).mono fun R hR s _ => ?_)
    simp only [max_eq_left hR]
  -- (vii) integrals
  have hint : ∀ R, R₀ ≤ R → IntegrableOn (maskedRate a Γ Ψ R) (Ioo 0 1) := fun R hR =>
    ((hcontOn R hR).integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hVIIb : ∀ R R', R₀ ≤ R → R ≤ R' →
      maskedIntegratedRate a Γ Ψ R ≤ maskedIntegratedRate a Γ Ψ R' ∧
      maskedIntegratedRate a Γ Ψ R' ≤ integratedRate a Γ Ψ := by
    intro R R' hR hRR
    have hR' : R₀ ≤ R' := hR.trans hRR
    refine ⟨setIntegral_mono_on (hint R hR) (hint R' hR') measurableSet_Ioo fun s hs =>
      (hII s (Ioo_subset_Icc_self hs) R R' (by linarith) hRR).1,
      setIntegral_mono_on (hint R' hR') hUint measurableSet_Ioo fun s hs =>
      (hII s (Ioo_subset_Icc_self hs) R' R' (by linarith) le_rfl).2⟩
  have hVIIc : Tendsto (maskedIntegratedRate a Γ Ψ) atTop (𝓝 (integratedRate a Γ Ψ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Real.sqrt M)
      ((eventually_ge_atTop R₀).mono fun R hR => (hint R hR).aestronglyMeasurable)
      ((eventually_ge_atTop R₀).mono fun R hR =>
        (ae_restrict_mem measurableSet_Ioo).mono fun s hs => ?_)
      (integrableOn_const (C := Real.sqrt M) (by simp))
      ((ae_restrict_mem measurableSet_Ioo).mono fun s hs => hV s (Ioo_subset_Icc_self hs))
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hmrate]; exact Real.sqrt_nonneg _)]
    exact (hI R hR s (Ioo_subset_Icc_self hs)).2.2.2.2.2.2
  exact ⟨ε, M, C, R₀, hε, hεM, hC, hR₀, hI, hII, hIII, hIV, hV, hVI, hint, hVIIb, hVIIc⟩

/-! ### The original point moment -/

/-- Auxiliary to the Lean proof route (the numerical supremum of TeX lines
217-218): if `J R → I` and, for all large `R`,
`2 J R - v/2 ≤ liminf_T L(T)` in `EReal`, then `2 I - v/2 ≤ liminf_T L(T)`.
No junk value: the liminf is taken in the complete lattice `EReal`. -/
theorem le_liminf_of_tendsto {J : ℝ → ℝ} {I v : ℝ} {L : ℝ → ℝ}
    (hJ : Tendsto J atTop (𝓝 I))
    (h : ∀ᶠ R in atTop, ((2 * J R - v / 2 : ℝ) : EReal) ≤
      liminf (fun T => (L T : EReal)) atTop) :
    ((2 * I - v / 2 : ℝ) : EReal) ≤ liminf (fun T => (L T : EReal)) atTop :=
  le_of_tendsto ((continuous_coe_real_ereal.tendsto _).comp
    ((hJ.const_mul 2).sub_const (v / 2))) h

/-- The named input for `E:variational-unmasked-point-lower`
(`P:raw-block-original-lower`, `notes/integrated_raw_block_lower.tex` lines
541-549 at a284420, applied with the mask `m_R` and read with the
identification of its ground rate with `maskedRate`; in the wrapper `v` is
`rawCost`, the integral form of `v_Ψ`): for all large `R`,
`liminf_{T→∞} L(T) ≥ 2 ∫_0^1 λ_{R,s} ds - v/2` in `EReal`, where `L(T)`
stands for `T^{-κ} log E|u(T,x)|²` at a fixed `x`. -/
def RawBlockOriginalLower (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) (v : ℝ)
    (L : ℝ → ℝ) : Prop :=
  ∀ᶠ R in atTop, ((2 * maskedIntegratedRate a Γ Ψ R - v / 2 : ℝ) : EReal) ≤
    liminf (fun T => (L T : EReal)) atTop

/-- **`E:variational-unmasked-point-lower`, general form** (TeX lines
175-178 and 214-218), over the named input `RawBlockOriginalLower` and the
hypotheses of `remove_mask`: for any real `v` and `L : ℝ → ℝ` with
`RawBlockOriginalLower a Γ Ψ v L`, `2 I_Ψ - v/2 ≤ liminf_{T→∞} L(T)` in
`EReal`. -/
theorem unmasked_point_lower {alpha : ℝ} {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hα : alpha < 2) (hΓ : Γ ≠ 0) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {v : ℝ} {L : ℝ → ℝ}
    (hRB : RawBlockOriginalLower a Γ Ψ v L) :
    ((2 * integratedRate a Γ Ψ - v / 2 : ℝ) : EReal) ≤ liminf (fun T => (L T : EReal)) atTop := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlim⟩ :=
    remove_mask hΓt hμt hsp hS hα hΓ ha0 ha hΨ
  exact le_liminf_of_tendsto hlim hRB

/-! ### The manuscript's statement -/

/-- The masks `m_R` (TeX lines 184-191) form an increasing family of
admissible radial masks tending to one: for `R > 0`, `m_R` is smooth, even,
radial, `[0,1]`-valued, equal to one on `|x| ≤ R` and supported in the closed
ball of radius `2R` (the eligibility conditions of
`notes/integrated_raw_block_lower.tex` lines 7-8 and
`notes/integrated_compact_mean_family.tex` lines 475-477, apart from the size
of `R`); `m_R ≤ m_{R'}` for `0 < R ≤ R'`; `m_R → 1` pointwise. -/
theorem mask_family :
    (∀ R, 0 < R →
      ContDiff ℝ ∞ (mask (d := d) R) ∧ (∀ x : Rd d, mask R (-x) = mask R x) ∧
      (∀ x y : Rd d, ‖x‖ = ‖y‖ → mask R x = mask R y) ∧
      (∀ x : Rd d, 0 ≤ mask R x ∧ mask R x ≤ 1) ∧ (∀ x : Rd d, ‖x‖ ≤ R → mask R x = 1) ∧
      tsupport (mask (d := d) R) ⊆ closedBall 0 (2 * R)) ∧
    (∀ R R', 0 < R → R ≤ R' → ∀ x : Rd d, mask R x ≤ mask R' x) ∧
    (∀ x : Rd d, Tendsto (fun R => mask R x) atTop (𝓝 1)) := by
  refine ⟨fun R hR => ⟨mask_contDiff hR, mask_neg R, fun x y h => mask_radial R h, mask_mem R,
    fun x hx => mask_eq_one hR hx, tsupport_mask_subset hR⟩,
    fun R R' hR hRR x => mask_mono hR hRR x, mask_tendsto⟩

/-- **`P:variational-remove-mask`, rate part** (TeX lines 168-174 and
181-212 of `notes/integrated_unmasked_variational.tex` at a284420), with the
section's standing hypotheses (line 4: a nonzero covariance satisfying
`H:homog`, `a = α₀`) and `Ψ ∈ C_pos`, `I = [0,1]`; no supplied input.  The
masks (`mask_family`) and, with `λ_{R,s}` DEFINED as the square root of the
real Rayleigh supremum of `m_R h_s` (`maskedRate`; `λ_{Ψ,s}` is
`VariationalDilation.rate`): reals `ε > 0`, `M ≥ ε`, `C ≥ 0`, `R₀ > 0` with
(i) for `R ≥ R₀` and `s ∈ I` the value set of `m_R h_s` nonempty and bounded
above with `ε ≤ λ_{R,s}² = sup ≤ M` (the common margin, lines 193-194) and
`√ε ≤ λ_{R,s} ≤ √M`; (ii) `λ_{R,s} ≤ λ_{R',s} ≤ λ_{Ψ,s}` for `0 < R ≤ R'`;
(iii) `|λ_{R,s} - λ_{R,t}| ≤ C/(2√ε) |s - t|` for `R ≥ R₀`; (iv) the
exchange display (lines 200-206) in the form
`sup_{R ≥ R₀} λ_{R,s}² = λ_{Ψ,s}²` (stated with the suprema of the value sets,
equal to the squared rates by (i) and `VariationalRate.unmasked_rate`);
(v) `λ_{R,s} → λ_{Ψ,s}` for every `s ∈ I`; (vi) uniformly on `I`;
(vii) `λ_{R,·}` integrable on `(0,1)` for `R ≥ R₀`, `∫_I λ_{R,s} ds`
nondecreasing in `R ≥ R₀` and at most `I_Ψ`, and `∫_I λ_{R,s} ds → I_Ψ`.
Narrower than the TeX: the rates are the Rayleigh rates; the TeX's compact
ground rates (`P:compact-ground-family` applied to `m_R h_s`) and their
identification with the Rayleigh form (lines 195-196) are not formalized
(foundation D8), as for `λ_{Ψ,s}` in `variational_unmasked_rate_paper`.
Of `H:homog`, the fields `Γ_tempered`, `μ_tempered`, `spectral`, `Γ_radon`,
`scaling`, `alpha0_pos`, `alpha0_lt_one`, `threshold` are used; `dim`,
`Γ_even`, `Γ_posdef`, `μ_radon`, `μ_even`, `alpha_range` are carried,
unused. -/
theorem variational_remove_mask_rates_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    (∀ R, 0 < R →
      ContDiff ℝ ∞ (mask (d := d) R) ∧ (∀ x : Rd d, mask R (-x) = mask R x) ∧
      (∀ x y : Rd d, ‖x‖ = ‖y‖ → mask R x = mask R y) ∧
      (∀ x : Rd d, 0 ≤ mask R x ∧ mask R x ≤ 1) ∧ (∀ x : Rd d, ‖x‖ ≤ R → mask R x = 1) ∧
      tsupport (mask (d := d) R) ⊆ closedBall 0 (2 * R)) ∧
    (∀ R R', 0 < R → R ≤ R' → ∀ x : Rd d, mask R x ≤ mask R' x) ∧
    (∀ x : Rd d, Tendsto (fun R => mask R x) atTop (𝓝 1)) ∧
    (∃ ε M C R₀ : ℝ, 0 < ε ∧ ε ≤ M ∧ 0 ≤ C ∧ 0 < R₀ ∧
      (∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1,
        (rayleighSet (maskedMean alpha0 Γ Ψ R s)).Nonempty ∧
        BddAbove (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        ε ≤ sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ≤ M ∧
        maskedRate alpha0 Γ Ψ R s ^ 2 = sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        Real.sqrt ε ≤ maskedRate alpha0 Γ Ψ R s ∧ maskedRate alpha0 Γ Ψ R s ≤ Real.sqrt M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ R R', 0 < R → R ≤ R' →
        maskedRate alpha0 Γ Ψ R s ≤ maskedRate alpha0 Γ Ψ R' s ∧
        maskedRate alpha0 Γ Ψ R' s ≤ rate alpha0 Γ Ψ s) ∧
      (∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |maskedRate alpha0 Γ Ψ R s - maskedRate alpha0 Γ Ψ R t| ≤
          C / (2 * Real.sqrt ε) * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        sSup ((fun R => sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s))) '' Ici R₀) =
          sSup (rayleighSet (mean alpha0 Γ Ψ s))) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        Tendsto (fun R => maskedRate alpha0 Γ Ψ R s) atTop (𝓝 (rate alpha0 Γ Ψ s))) ∧
      TendstoUniformlyOn (fun R s => maskedRate alpha0 Γ Ψ R s) (rate alpha0 Γ Ψ) atTop (Icc 0 1) ∧
      (∀ R, R₀ ≤ R → IntegrableOn (maskedRate alpha0 Γ Ψ R) (Ioo 0 1)) ∧
      (∀ R R', R₀ ≤ R → R ≤ R' →
        maskedIntegratedRate alpha0 Γ Ψ R ≤ maskedIntegratedRate alpha0 Γ Ψ R' ∧
        maskedIntegratedRate alpha0 Γ Ψ R' ≤ integratedRate alpha0 Γ Ψ) ∧
      Tendsto (maskedIntegratedRate alpha0 Γ Ψ) atTop (𝓝 (integratedRate alpha0 Γ Ψ))) := by
  have := hH.Γ_radon
  exact ⟨mask_family.1, mask_family.2.1, mask_family.2.2,
    remove_mask hH.Γ_tempered hH.μ_tempered hH.spectral hH.scaling (alpha_lt_two hH) hΓ0
      hH.alpha0_pos.le hH.alpha0_lt_one hΨ⟩

/-- **`P:variational-remove-mask`** (TeX lines 168-221 of
`notes/integrated_unmasked_variational.tex` at a284420), with the section's
standing hypotheses (line 4: a nonzero covariance satisfying `H:homog`,
`a = α₀`), `Ψ ∈ C_pos`, `I = [0,1]`, and the named input
`RawBlockOriginalLower` (see its doc comment) for a function `L`, where
`L(T)` stands for `T^{-κ} log E|u(T,x)|²` at a fixed `x`.  Conclusions: the
rate part of `variational_remove_mask_rates_paper` and
`E:variational-unmasked-point-lower` (lines 175-178) in the form
`2 I_Ψ - v_Ψ/2 ≤ liminf_{T→∞} L(T)` in `EReal`, with `v_Ψ` the integral form
`VariationalDilation.rawCost` of `E:compact-raw-cost`.  Narrower than the TeX:
the canonical solution `u` and its moment are not defined in Lean; the
display relates the same `L` that the named input bounds (lines 214-218, the
numerical supremum over the individual bounds).  The rate convention and the
`H:homog` fields used are as in `variational_remove_mask_rates_paper`. -/
theorem variational_remove_mask_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) {L : ℝ → ℝ}
    (hRB : RawBlockOriginalLower alpha0 Γ Ψ (rawCost alpha0 Γ Ψ) L) :
    (∀ R, 0 < R →
      ContDiff ℝ ∞ (mask (d := d) R) ∧ (∀ x : Rd d, mask R (-x) = mask R x) ∧
      (∀ x y : Rd d, ‖x‖ = ‖y‖ → mask R x = mask R y) ∧
      (∀ x : Rd d, 0 ≤ mask R x ∧ mask R x ≤ 1) ∧ (∀ x : Rd d, ‖x‖ ≤ R → mask R x = 1) ∧
      tsupport (mask (d := d) R) ⊆ closedBall 0 (2 * R)) ∧
    (∀ R R', 0 < R → R ≤ R' → ∀ x : Rd d, mask R x ≤ mask R' x) ∧
    (∀ x : Rd d, Tendsto (fun R => mask R x) atTop (𝓝 1)) ∧
    (∃ ε M C R₀ : ℝ, 0 < ε ∧ ε ≤ M ∧ 0 ≤ C ∧ 0 < R₀ ∧
      (∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1,
        (rayleighSet (maskedMean alpha0 Γ Ψ R s)).Nonempty ∧
        BddAbove (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        ε ≤ sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ≤ M ∧
        maskedRate alpha0 Γ Ψ R s ^ 2 = sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s)) ∧
        Real.sqrt ε ≤ maskedRate alpha0 Γ Ψ R s ∧ maskedRate alpha0 Γ Ψ R s ≤ Real.sqrt M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ R R', 0 < R → R ≤ R' →
        maskedRate alpha0 Γ Ψ R s ≤ maskedRate alpha0 Γ Ψ R' s ∧
        maskedRate alpha0 Γ Ψ R' s ≤ rate alpha0 Γ Ψ s) ∧
      (∀ R, R₀ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |maskedRate alpha0 Γ Ψ R s - maskedRate alpha0 Γ Ψ R t| ≤
          C / (2 * Real.sqrt ε) * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        sSup ((fun R => sSup (rayleighSet (maskedMean alpha0 Γ Ψ R s))) '' Ici R₀) =
          sSup (rayleighSet (mean alpha0 Γ Ψ s))) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        Tendsto (fun R => maskedRate alpha0 Γ Ψ R s) atTop (𝓝 (rate alpha0 Γ Ψ s))) ∧
      TendstoUniformlyOn (fun R s => maskedRate alpha0 Γ Ψ R s) (rate alpha0 Γ Ψ) atTop (Icc 0 1) ∧
      (∀ R, R₀ ≤ R → IntegrableOn (maskedRate alpha0 Γ Ψ R) (Ioo 0 1)) ∧
      (∀ R R', R₀ ≤ R → R ≤ R' →
        maskedIntegratedRate alpha0 Γ Ψ R ≤ maskedIntegratedRate alpha0 Γ Ψ R' ∧
        maskedIntegratedRate alpha0 Γ Ψ R' ≤ integratedRate alpha0 Γ Ψ) ∧
      Tendsto (maskedIntegratedRate alpha0 Γ Ψ) atTop (𝓝 (integratedRate alpha0 Γ Ψ))) ∧
    ((2 * integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 : ℝ) : EReal) ≤
      liminf (fun T => (L T : EReal)) atTop := by
  have := hH.Γ_radon
  exact ⟨(variational_remove_mask_rates_paper hH hΓ0 hΨ).1,
    (variational_remove_mask_rates_paper hH hΓ0 hΨ).2.1,
    (variational_remove_mask_rates_paper hH hΓ0 hΨ).2.2.1,
    (variational_remove_mask_rates_paper hH hΓ0 hΨ).2.2.2,
    unmasked_point_lower hH.Γ_tempered hH.μ_tempered hH.spectral hH.scaling (alpha_lt_two hH)
      hΓ0 hH.alpha0_pos.le hH.alpha0_lt_one hΨ hRB⟩

end StratonovichHAMSecondMoment.RemoveMask
