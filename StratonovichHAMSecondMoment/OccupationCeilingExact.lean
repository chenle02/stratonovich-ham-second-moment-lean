module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave item L9-A2: Lemma `L:occupation-rayleigh-selection` (Countable Rayleigh
near-occupations; `notes/integrated_occupation_ceiling.tex` at revision a284420, statement
lines 149-157, proof lines 159-193) and Theorem `T:intrinsic-occupation-ceiling` (The computed
occupation ceiling; statement lines 205-220, proof lines 222-250) with the EXACT constant
`C_occ` of `P:raw-occupation-energy` (module `RawOccupationEnergy`, item L9-A1), in both forms,
for the variational values `S_c^pos`; with them the comparison of
`C:intrinsic-spatial-bracket` (lines 261-265, proof 275-290) for `S_2^pos`.  Standing
assumptions (lines 4-21): `H:homog` (`HomogHypothesis.HomogCovariance d α α₀ Γ μ`), `a = α₀`,
`Γ ≠ 0` (line 20); `q = 4-α`, `k = 3-α`, `m = q/k`.

Objects reused, not redefined: `𝒪 = OccupationPhysicalClass.IsOccField`, `T(g)`,
`A(g) = RawOccupationEnergy.A`, `C_occ = RawOccupationEnergy.Cocc`,
`𝓔_ζ^𝒪 = RawOccupationEnergy.EO`, `C_pos = VariationalDilation.CPos`,
`h_{Ψ,s} = VariationalDilation.mean`, `v_Ψ = VariationalDilation.rawCost`,
`I_Ψ = VariationalDilation.integratedRate`, `S_c^pos = sSup (VariationalRate.scoreSet α₀ Γ c)`,
`U_c = SpatialBracket.ceilingValue α c C_occ` (`E:occupation-score-ceiling`, lines 209-212),
`F_0 = SpatialFourLinear.F0`, `F_b = SpatialBracket.Fb` (`E:occupation-scalar-map`, lines
195-201).  Lean route objects (auxiliary): the trapezoids `trap`, the cell index `idx`, the
cell indicators `cellInd`, and the finite-cell field `stepG`/`stepDG`.

Formalized (exact-hypothesis wrappers over `H:homog` with `a = α₀` and `Γ ≠ 0`):
* `occupation_rayleigh_selection_paper` (`E:occupation-rayleigh-selection`): for `Ψ ∈ C_pos`
  and `ε > 0` there is `g_ε ∈ 𝒪` with `I_Ψ² + T(g_ε) ≤ √(v_Ψ A(g_ε)) + ε`.
* `intrinsic_occupation_ceiling_paper`: for every `c > 0` (the coefficient range of
  `P:variational-positive-scores`, `integrated_unmasked_variational.tex` line 272) the value set
  is nonempty and bounded above, `c I_Ψ - v_Ψ/2 ≤ U_c` for every `Ψ ∈ C_pos`,
  `S_c^pos ≤ U_c = c^m k[α^{α/2} C_occ/(8q^{q/2})]^{1/k}`, and
  `U_c = c^m (2ζ)^{α/(2k)} F_0(𝓔_ζ^𝒪)` for every `ζ > 0`.
* `intrinsic_spatial_comparison_paper` (B13): `S_2^pos ≤ 2^m F_0(𝓔_{1/2}^𝒪) <
  2^m F_a(𝓔_{1/2}^𝒪)`, the value set at `c = 2` being nonempty and bounded above.
* Route steps: `step_mean_le_sqrt` (`∫_0^1 ∫ h_{Ψ,s} g_s² ≤ √(v_Ψ A(g))` for the finite-cell
  field, the final display of `L:occupation-raw-square`, lines 38-41, for that field),
  `stepField_isOcc`, `integratedRate_sq_le_Cocc` (lines 223-234), `score_le_ceiling_Cocc`
  (lines 235-243), `A_le_Cocc`.

Supplied inputs: none.  `S1Bdd` is never assumed; the named input `SpaceTimePosDef` is not
used.  The space-time Cauchy-Schwarz bound is wave item L8-c1's
`SpaceTimePositivity.integral_mean_mul_le_sqrt`, proved for continuous compactly supported
fields; the finite-cell field is not continuous in time, so `step_mean_le_sqrt` approximates its
cell indicators by continuous trapezoids and passes to the limit by dominated convergence on both
sides (no extension of L8-c1's positivity proof is needed).

Narrower than the TeX (recorded): the moment sentence `C_2(Γ,a) ≤ U_2` (line 217) and the
`C_2` form of the comparison (lines 263-264) are not formalized (they need
`T:intrinsic-second-moment`, `C_2 = S_2^pos`, foundation D1): the statements are for `S_c^pos`
and `S_2^pos`; the class `𝒪` is modelled by joint representatives (`IsOccField`), as in
`P:raw-occupation-energy`; the direct zero case `Γ = 0` (lines 302-308) is not formalized.

Route differences (decision 2 of wave L9): in `L:occupation-rayleigh-selection` the TeX's
countable dense family with a first-index Borel selection (lines 160-173) is replaced by `N+1`
equal time cells with near-optimal real unit tests at the left nodes
(`OccupationCeilingFinite.exists_unitTest_gt`) and the uniform Lipschitz bounds in `s` of
`∫ h_s f²` (`L:variational-global-mean`) and of `λ_s²` (`P:variational-unmasked-rate`); the
field `g_s = f_j` on cell `j` is a finite simple field of unit tests, hence in `𝒪`.  The bound
`⟨Ψ,ρ_g⟩ ≤ √(v_Ψ A(g))` is `step_mean_le_sqrt` (above) instead of the map `Q` and `ρ_g ∈ H_I` of
`L:occupation-raw-square`, which are not formalized.  The rest follows the TeX: `I_Ψ² ≤ ∫_0^1 λ_s²`
(by Jensen; the TeX's time Cauchy-Schwarz, lines 188-189), the two scalar maxima by weighted AM-GM
(`OccupationCeilingFinite.young_quarter`, `young_q`), the positive-power algebra
(`OccupationCeilingFinite.ceilingValue_eq`), the second form by `E:raw-occupation-energy`
and `SpatialBracket.ceilingValue_eq_zeta`, and `F_0 < F_a` (`SpatialBracket.F0_lt_Fa`, `Δ > 0`).

Implicit hypotheses made explicit: integrability of every time integrand is proved; `S_c^pos`
is used only with nonemptiness and boundedness proved; `T(g) > 0` on `𝒪` (`d ≥ 1`).
`step_mean_le_sqrt` passes its `Γ ≠ 0` only to `VariationalMean.variational_global_mean_paper`,
which carries it unused.  Lemmas marked "Auxiliary to the Lean proof route" have no manuscript
label.  The fallback scope was not needed.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.RawOccupationEnergy
public import StratonovichHAMSecondMoment.SpaceTimePositivity

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StratonovichHAMSecondMoment.OccupationCeilingExact

open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open OccupationPhysicalClass (volI sqPair gradSqE Tlin T IsOccField)
open TimeSchur (kern kern_nonneg measurable_kern)
open SpatialFourierBound (spatialPair gradEnergy IsUnitTest)
open WeakSobolev (IsTestFunction rayleighSet)
open VariationalDilation (CPos mean rawCost rate integratedRate)
open VariationalRate (scoreSet)
open VariationalFloor (grad)
open RawOccupationEnergy (Araw A Cocc EO ratioSet)
open OccupationCeilingFinite (fieldG fieldG_props)

variable {d : ℕ}

/-! ### Trapezoids in time (auxiliary) -/

/-- Auxiliary to the Lean proof route: the continuous trapezoid
`s ↦ max 0 (min 1 ((n+1) min(s-p, q-s)))`, which increases to the indicator of `(p,q)`. -/
def trap (n : ℕ) (p q s : ℝ) : ℝ := max 0 (min 1 (((n : ℝ) + 1) * min (s - p) (q - s)))

/-- Auxiliary to the Lean proof route: the trapezoid is continuous. -/
theorem trap_continuous (n : ℕ) (p q : ℝ) : Continuous (trap n p q) :=
  continuous_const.max (continuous_const.min (continuous_const.mul
    ((continuous_id.sub continuous_const).min (continuous_const.sub continuous_id))))

/-- Auxiliary to the Lean proof route: `0 ≤ trap ≤ 1`. -/
theorem trap_mem (n : ℕ) (p q s : ℝ) : 0 ≤ trap n p q s ∧ trap n p q s ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- Auxiliary to the Lean proof route: the trapezoid vanishes off `(p,q)`. -/
theorem trap_eq_zero {n : ℕ} {p q s : ℝ} (hs : s ∉ Ioo p q) : trap n p q s = 0 := by
  have hm : min (s - p) (q - s) ≤ 0 := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have h : ((n : ℝ) + 1) * min (s - p) (q - s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hm
  unfold trap
  exact max_eq_left ((min_le_right _ _).trans h)

/-- Auxiliary to the Lean proof route: the trapezoid has compact support. -/
theorem trap_hasCompactSupport (n : ℕ) (p q : ℝ) : HasCompactSupport (trap n p q) :=
  HasCompactSupport.intro (isCompact_Icc (a := p) (b := q)) fun _ hs =>
    trap_eq_zero fun h => hs (Ioo_subset_Icc_self h)

/-- Auxiliary to the Lean proof route: `trap n p q s → 1_{(p,q)}(s)` for every `s`. -/
theorem trap_tendsto (p q s : ℝ) :
    Tendsto (fun n => trap n p q s) atTop (𝓝 ((Ioo p q).indicator (fun _ => (1 : ℝ)) s)) := by
  by_cases hs : s ∈ Ioo p q
  · rw [indicator_of_mem hs]
    set m := min (s - p) (q - s) with hmdef
    have hm : 0 < m := lt_min (by linarith [hs.1]) (by linarith [hs.2])
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / m)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop K] with n hn
    have hKn : (K : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 1 ≤ ((n : ℝ) + 1) * m := by
      have : 1 / m < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hm] at this
      linarith
    have : trap n p q s = 1 := by
      unfold trap
      rw [← hmdef, min_eq_left h1, max_eq_right zero_le_one]
    exact this.symm
  · rw [indicator_of_notMem hs]
    simp only [trap_eq_zero hs]
    exact tendsto_const_nhds

/-! ### Equal time cells (auxiliary) -/

/-- Auxiliary to the Lean proof route: the index `min(⌊(N+1)s⌋, N)` of the cell of `s` among
the `N+1` equal cells of `[0,1]`. -/
def idx (N : ℕ) (s : ℝ) : Fin (N + 1) :=
  ⟨min ⌊((N : ℝ) + 1) * s⌋₊ N, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Auxiliary to the Lean proof route: the cell index is measurable. -/
theorem idx_measurable (N : ℕ) : Measurable (idx N) := by
  have h : idx N = (fun k : ℕ => (⟨min k N, Nat.lt_succ_of_le (min_le_right _ _)⟩ :
      Fin (N + 1))) ∘ (fun s : ℝ => ⌊((N : ℝ) + 1) * s⌋₊) := rfl
  rw [h]
  exact measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_const_mul _))

/-- Auxiliary to the Lean proof route: the left node of the cell of `s ∈ [0,1]` is within
`1/(N+1)` of `s`. -/
theorem idx_close {N : ℕ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    |s - ((idx N s : ℕ) : ℝ) / ((N : ℝ) + 1)| ≤ 1 / ((N : ℝ) + 1) := by
  set k := ⌊((N : ℝ) + 1) * s⌋₊ with hk
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hx0 : 0 ≤ ((N : ℝ) + 1) * s := mul_nonneg hN.le hs.1
  have hk1 : (k : ℝ) ≤ ((N : ℝ) + 1) * s := Nat.floor_le hx0
  have hk2 : ((N : ℝ) + 1) * s < k + 1 := Nat.lt_floor_add_one _
  have hj : ((idx N s : ℕ) : ℝ) = ((min k N : ℕ) : ℝ) := rfl
  have h1 : ((min k N : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * s :=
    (Nat.cast_le.2 (min_le_left _ _)).trans hk1
  have h2 : ((N : ℝ) + 1) * s ≤ ((min k N : ℕ) : ℝ) + 1 := by
    rcases le_total k N with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; nlinarith [hs.2]
  rw [hj, abs_le]
  constructor
  · have : ((min k N : ℕ) : ℝ) / ((N : ℝ) + 1) ≤ s := by rw [div_le_iff₀ hN]; linarith
    have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    linarith
  · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN]
    linarith

/-- Auxiliary to the Lean proof route: off the nodes `k/(N+1)`, `s ∈ (0,1)` lies in the open
cell `(j/(N+1), (j+1)/(N+1))` exactly when its index is `j`. -/
theorem idx_eq_iff {N : ℕ} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hnode : ∀ k : ℕ, ((N : ℝ) + 1) * s ≠ k) (j : Fin (N + 1)) :
    idx N s = j ↔
      s ∈ Ioo (((j : ℕ) : ℝ) / ((N : ℝ) + 1)) ((((j : ℕ) : ℝ) + 1) / ((N : ℝ) + 1)) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  set x := ((N : ℝ) + 1) * s with hx
  have hx0 : 0 ≤ x := mul_nonneg hN.le hs.1.le
  have hx1 : x < (N : ℝ) + 1 := by rw [hx]; nlinarith [hs.2]
  have hkN : ⌊x⌋₊ ≤ N := by
    have h : (⌊x⌋₊ : ℝ) < (N : ℝ) + 1 := (Nat.floor_le hx0).trans_lt hx1
    have h' : ⌊x⌋₊ < N + 1 := by exact_mod_cast h
    omega
  have hval : (idx N s : ℕ) = ⌊x⌋₊ := min_eq_left hkN
  rw [Fin.ext_iff, hval, Nat.floor_eq_iff hx0, mem_Ioo, div_lt_iff₀ hN, lt_div_iff₀ hN,
    mul_comm s]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_le_of_ne h1 (fun h => hnode _ h.symm), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.le, h2⟩

/-- Auxiliary to the Lean proof route: Lebesgue-a.e. `s` is off every node `k/(N+1)`. -/
theorem ae_offNode (N : ℕ) : ∀ᵐ s ∂(volume : Measure ℝ), ∀ k : ℕ, ((N : ℝ) + 1) * s ≠ k := by
  rw [ae_all_iff]
  intro k
  filter_upwards [Measure.ae_ne volume ((k : ℝ) / ((N : ℝ) + 1))] with s hs h
  apply hs
  rw [eq_div_iff (by positivity)]
  linarith

/-- Auxiliary to the Lean proof route: the cell indicator `1_{(j/(N+1),(j+1)/(N+1))}`. -/
def cellInd (N : ℕ) (j : Fin (N + 1)) (s : ℝ) : ℝ :=
  (Ioo (((j : ℕ) : ℝ) / ((N : ℝ) + 1)) ((((j : ℕ) : ℝ) + 1) / ((N : ℝ) + 1))).indicator
    (fun _ => (1 : ℝ)) s

/-- Auxiliary to the Lean proof route: off the nodes in `(0,1)`, `∑_j 1_j(s) w_j = w_{idx s}`. -/
theorem sum_cellInd {N : ℕ} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hnode : ∀ k : ℕ, ((N : ℝ) + 1) * s ≠ k) (w : Fin (N + 1) → ℝ) :
    ∑ j, cellInd N j s * w j = w (idx N s) := by
  rw [Finset.sum_eq_single (idx N s)]
  · rw [cellInd, indicator_of_mem ((idx_eq_iff hs hnode _).1 rfl), one_mul]
  · intro j _ hj
    rw [cellInd, indicator_of_notMem (fun h => hj ((idx_eq_iff hs hnode j).2 h).symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The step field (auxiliary) -/

/-- The finite-cell field `g_s = f_j` for `s` in cell `j` (TeX: the selected field `g_ε` of
`L:occupation-rayleigh-selection`, lines 159-173, built here from finitely many equal cells
instead of a countable first-index selection). -/
def stepG (N : ℕ) (f : Fin (N + 1) → Rd d → ℝ) : ℝ → Rd d → ℝ := fun s => f (idx N s)

/-- The gradient field of `stepG`: `∇g_s = ∇f_j` on cell `j`. -/
def stepDG (N : ℕ) (f : Fin (N + 1) → Rd d → ℝ) : ℝ → Rd d → Rd d :=
  fun s => grad (f (idx N s))

/-- Auxiliary to the Lean proof route: `b(f) = ∫ ‖∇f‖²` as an extended integral for a real unit
test. -/
theorem gradSqE_grad {g : Rd d → ℝ} (hg : IsUnitTest g) :
    gradSqE (grad g) = ENNReal.ofReal (gradEnergy g) := by
  rw [(OccupationPhysicalClass.gradSqE_eq
    (SpatialStaticControls.isUnitH1_of_unitTest hg).2.1).2]
  congr 1
  unfold SpatialFourierBound.gradEnergy VariationalFloor.grad
  congr 1; funext x
  rw [LinearIsometryEquiv.norm_map]

/-- The finite-cell field lies in `𝒪` (TeX lines 170-181: it is strongly measurable and has
finite gradient budget; here it is a finite simple field of unit tests) and
`T(g) = ∫_0^1 b(f_{j(s)}) ds`. -/
theorem stepField_isOcc {N : ℕ} {f : Fin (N + 1) → Rd d → ℝ} (hf : ∀ j, IsUnitTest (f j)) :
    IsOccField (stepG N f) (stepDG N f) ∧
      T (stepDG N f) = ∫ s, gradEnergy (f (idx N s)) ∂volI := by
  have hb : Measurable fun s => gradEnergy (f (idx N s)) :=
    (measurable_of_finite (fun j => gradEnergy (f j))).comp (idx_measurable N)
  have hb0 : ∀ j, 0 ≤ gradEnergy (f j) := fun j => SpatialFourierBound.gradEnergy_nonneg _
  have hTl : Tlin (stepDG N f) = ∫⁻ s, ENNReal.ofReal (gradEnergy (f (idx N s))) ∂volI := by
    unfold Tlin stepDG
    simp_rw [gradSqE_grad (hf _)]
  refine ⟨⟨?_, ?_, Eventually.of_forall fun s => SpatialStaticControls.isUnitH1_of_unitTest
    (hf _), ?_⟩, ?_⟩
  · have hF : Measurable (fun q : Rd d × Fin (N + 1) => f q.2 q.1) :=
      measurable_from_prod_countable_left fun j => (hf j).1.continuous.measurable
    exact (hF.comp (measurable_snd.prodMk
      ((idx_measurable N).comp measurable_fst))).aestronglyMeasurable
  · have hF : Measurable (fun q : Rd d × Fin (N + 1) => grad (f q.2) q.1) :=
      measurable_from_prod_countable_left fun j =>
        (VariationalFloor.continuous_grad ⟨(hf j).1, (hf j).2.1⟩).measurable
    exact (hF.comp (measurable_snd.prodMk
      ((idx_measurable N).comp measurable_fst))).aestronglyMeasurable
  · rw [hTl]
    calc ∫⁻ s, ENNReal.ofReal (gradEnergy (f (idx N s))) ∂volI
        ≤ ∫⁻ _, ENNReal.ofReal (∑ j, gradEnergy (f j)) ∂volI := by
          refine lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_
          exact Finset.single_le_sum (fun j _ => hb0 j) (Finset.mem_univ _)
      _ < ⊤ := by
          rw [lintegral_const, OccupationPhysicalClass.volI_univ, mul_one]
          exact ENNReal.ofReal_lt_top
  · unfold T
    rw [hTl, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => hb0 _)
      hb.aestronglyMeasurable]

/-! ### The Cauchy-Schwarz bound for the step field (auxiliary) -/

/-- Auxiliary to the Lean proof route: for a unit test `g` and `0 ≤ h ≤ M`,
`0 ≤ ∫ h g² ≤ M`. -/
theorem mean_pair_bound {V : Rd d → ℝ} {M : ℝ} (hV : ∀ x, 0 ≤ V x ∧ V x ≤ M)
    {g : Rd d → ℝ} (hg : IsUnitTest g) (hi : Integrable (fun x => V x * g x ^ 2) volume) :
    0 ≤ ∫ x, V x * g x ^ 2 ∧ ∫ x, V x * g x ^ 2 ≤ M := by
  have hsqt := SpatialFourLinear.isTest_sq (φ := g) ⟨hg.1, hg.2.1⟩
  have hsq : Integrable (fun x => g x ^ 2) volume :=
    hsqt.1.continuous.integrable_of_hasCompactSupport hsqt.2
  refine ⟨integral_nonneg fun x => mul_nonneg (hV x).1 (sq_nonneg _), ?_⟩
  calc ∫ x, V x * g x ^ 2 ≤ ∫ x, M * g x ^ 2 :=
        integral_mono hi (hsq.const_mul M) fun x =>
          mul_le_mul_of_nonneg_right (hV x).2 (sq_nonneg _)
    _ = M := by rw [integral_const_mul, hg.2.2, mul_one]

/-- **The Cauchy-Schwarz bound for the finite-cell field** (auxiliary to the Lean route; the
final display of `L:occupation-raw-square`, `integrated_occupation_ceiling.tex` lines 38-41,
`⟨Ψ,ρ_g⟩ ≤ √(v_Ψ A(g))` in its integral form, for the step field `g`).  Under `H:homog` with
`a = α₀` and `Γ ≠ 0`, for `Ψ ∈ C_pos` and real unit tests `f_j`:
`∫_0^1 ∫ h_{Ψ,s} g_s² dx ds ≤ √(v_Ψ A(g))`.  Route (not the TeX's map `Q` and `ρ_g ∈ H_I`):
the cell indicators are limits of continuous trapezoids `χ_j^n`; for the continuous fields
`Φ_n = ∑_j χ_j^n f_j²` the bound is `SpaceTimePositivity.integral_mean_mul_le_sqrt` (wave
item L8-c1); both sides pass to the limit by dominated convergence (the left in time with
bound `(N+1) M`, the right on `(0,1)²` with bound `|s-t|^{-a} ∑ |B_Γ(f_i², f_j²)|`), and the
limits are `∫∫ h g²` and `A(g)`. -/
theorem step_mean_le_sqrt {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d)
    {N : ℕ} {f : Fin (N + 1) → Rd d → ℝ} (hf : ∀ j, IsUnitTest (f j)) :
    ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ s x * stepG N f s x ^ 2 ≤
      Real.sqrt (rawCost a Γ Ψ * A a Γ (stepG N f)) := by
  have := hH.Γ_radon
  have ha0 := hH.alpha0_pos
  have ha1 := hH.alpha0_lt_one
  obtain ⟨M, CΨ, hM, hCΨ, -, -, hbd, hlipx, -, hpot⟩ :=
    VariationalMean.variational_global_mean_paper hH hΓ0 hΨ
  have : IsProbabilityMeasure volI := ⟨by simp⟩
  -- the pieces
  set m : Fin (N + 1) → ℝ → ℝ := fun j s => ∫ x, mean a Γ Ψ s x * f j x ^ 2 with hmdef
  set B : Fin (N + 1) → Fin (N + 1) → ℝ :=
    fun i j => spatialPair Γ (fun x => f i x ^ 2) (fun x => f j x ^ 2) with hBdef
  set χ : ℕ → Fin (N + 1) → ℝ → ℝ := fun n j =>
    trap n (((j : ℕ) : ℝ) / ((N : ℝ) + 1)) ((((j : ℕ) : ℝ) + 1) / ((N : ℝ) + 1)) with hχdef
  have hχc : ∀ n j, Continuous (χ n j) := fun n j => trap_continuous _ _ _
  have hχs : ∀ n j, HasCompactSupport (χ n j) := fun n j => trap_hasCompactSupport _ _ _
  have hχ0 : ∀ n j s, 0 ≤ χ n j s := fun n j s => (trap_mem _ _ _ _).1
  have hχ1 : ∀ n j s, χ n j s ≤ 1 := fun n j s => (trap_mem _ _ _ _).2
  have hχlim : ∀ j s, Tendsto (fun n => χ n j s) atTop (𝓝 (cellInd N j s)) := fun j s =>
    trap_tendsto _ _ _
  have hft : ∀ j, IsTestFunction (f j) := fun j => ⟨(hf j).1, (hf j).2.1⟩
  have hL2 : ∀ j, MemLp (f j) 2 volume := fun j => VariationalFloor.memLp_test (hft j)
  have hsq : ∀ j, Continuous fun x => f j x ^ 2 := fun j => (hf j).1.continuous.pow 2
  have hsqs : ∀ j, HasCompactSupport fun x => f j x ^ 2 := fun j =>
    (hf j).2.1.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j =>
    OccupationCeilingFinite.spatialPair_nonneg Γ (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hmb : ∀ j, ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ m j s ∧ m j s ≤ M := fun j s hs =>
    mean_pair_bound (hbd s hs) (hf j) (hpot s hs _ (hL2 j))
  have hmc : ∀ j, ContinuousOn (m j) (Icc 0 1) := by
    intro j
    refine OccupationCeilingFinite.continuousOn_of_lip hCΨ fun s hs t ht => ?_
    have e : m j s - m j t = ∫ x, (mean a Γ Ψ s x - mean a Γ Ψ t x) * f j x ^ 2 := by
      simp only [hmdef]
      rw [← integral_sub (hpot s hs _ (hL2 j)) (hpot t ht _ (hL2 j))]
      congr 1; funext x; ring
    have hsqi : Integrable (fun x => f j x ^ 2) volume :=
      (hsq j).integrable_of_hasCompactSupport (hsqs j)
    rw [e, ← Real.norm_eq_abs]
    calc _ ≤ ∫ x, CΨ * |s - t| * f j x ^ 2 :=
          norm_integral_le_of_norm_le (hsqi.const_mul _) (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (f j x))]
            exact mul_le_mul_of_nonneg_right (hlipx s hs t ht x) (sq_nonneg _))
      _ = CΨ * |s - t| := by rw [integral_const_mul, (hf j).2.2, mul_one]
  have hIoo : ∀ᵐ s ∂volI, s ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  have hoff : ∀ᵐ s ∂volI, ∀ k : ℕ, ((N : ℝ) + 1) * s ≠ k := ae_restrict_of_ae (ae_offNode N)
  -- the continuous fields
  set Φ : ℕ → ℝ × Rd d → ℝ := fun n => fieldG (χ n) f with hΦdef
  have hΦ : ∀ n, Continuous (Φ n) ∧ HasCompactSupport (Φ n) ∧ ∀ p, 0 ≤ Φ n p := fun n =>
    fieldG_props (hχc n) (hχs n) (hχ0 n) hft
  have hCS : ∀ n, ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ s x * Φ n (s, x) ≤
      Real.sqrt (rawCost a Γ Ψ * SpaceTimePositivity.stForm a Γ (Φ n) (Φ n)) := fun n =>
    (SpaceTimePositivity.integral_mean_mul_le_sqrt ha0 ha1 hH.Γ_even hH.spectral
      hΨ.1.continuous hΨ.2.1 (hΦ n).1 (hΦ n).2.1).2.2
  -- left side: inner integrals and dominated convergence in time
  have hinner : ∀ n, ∀ s ∈ Icc (0 : ℝ) 1,
      ∫ x, mean a Γ Ψ s x * Φ n (s, x) = ∑ j, χ n j s * m j s := by
    intro n s hs
    show ∫ x, mean a Γ Ψ s x * ∑ j, χ n j s * f j x ^ 2 = _
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ =>
      ((hpot s hs _ (hL2 j)).const_mul (χ n j s)).congr (ae_of_all _ fun x => by ring)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hmdef]
    rw [← integral_const_mul]; congr 1; funext x; ring
  have hLn : ∀ n, ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ s x * Φ n (s, x) =
      ∫ s, ∑ j, χ n j s * m j s ∂volI := fun n =>
    setIntegral_congr_fun measurableSet_Ioo fun s hs => hinner n s (Ioo_subset_Icc_self hs)
  have hLlim : Tendsto (fun n => ∫ s, ∑ j, χ n j s * m j s ∂volI) atTop
      (𝓝 (∫ s, m (idx N s) s ∂volI)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∑ _j : Fin (N + 1), M)
      (fun n => ?_) (integrable_const _) (fun n => ?_) ?_
    · exact ((continuousOn_finsetSum _ fun j _ => (hχc n j).continuousOn.mul (hmc j)).mono
        Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [hIoo] with s hs
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have hb := hmb j s (Ioo_subset_Icc_self hs)
      rw [norm_mul, Real.norm_of_nonneg (hχ0 n j s), Real.norm_of_nonneg hb.1]
      calc χ n j s * m j s ≤ 1 * M := mul_le_mul (hχ1 n j s) hb.2 hb.1 zero_le_one
        _ = M := one_mul M
    · filter_upwards [hIoo, hoff] with s hs hn
      rw [← sum_cellInd hs hn (fun j => m j s)]
      exact tendsto_finsetSum _ fun j _ => (hχlim j s).mul tendsto_const_nhds
  have hP : ∫ s, m (idx N s) s ∂volI =
      ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ s x * stepG N f s x ^ 2 := rfl
  -- right side: the space-time forms and dominated convergence on `(0,1)²`
  have hpair : ∀ n (p : ℝ × ℝ), SpaceTimePositivity.stPair Γ (Φ n) (Φ n) p =
      ∑ i, ∑ j, χ n i p.1 * χ n j p.2 * B i j := by
    intro n p
    show spatialPair Γ (fun x => ∑ i, χ n i p.1 * f i x ^ 2)
      (fun x => ∑ j, χ n j p.2 * f j x ^ 2) = _
    exact OccupationCeilingFinite.spatialPair_fsum Γ _ _ hsq hsqs hsq hsqs
  set Bs : ℝ := ∑ i, ∑ j, B i j with hBs
  have hkint := SpaceTimePositivity.kern_integrable ha1
  have hkm : Measurable fun p : ℝ × ℝ => kern a (p.1 - p.2) :=
    (measurable_kern a).comp (measurable_fst.sub measurable_snd)
  have hBidx : Measurable fun p : ℝ × ℝ => B (idx N p.1) (idx N p.2) :=
    (measurable_of_finite (fun q : Fin (N + 1) × Fin (N + 1) => B q.1 q.2)).comp
      (((idx_measurable N).comp measurable_fst).prodMk ((idx_measurable N).comp measurable_snd))
  have hBle : ∀ p : ℝ × ℝ, B (idx N p.1) (idx N p.2) ≤ Bs := by
    intro p
    calc B (idx N p.1) (idx N p.2) ≤ ∑ j, B (idx N p.1) j :=
          Finset.single_le_sum (fun j _ => hB0 _ j) (Finset.mem_univ _)
      _ ≤ Bs := Finset.single_le_sum (f := fun i => ∑ j, B i j)
          (fun i _ => Finset.sum_nonneg fun j _ => hB0 i j) (Finset.mem_univ _)
  have hSlim : Tendsto (fun n => SpaceTimePositivity.stForm a Γ (Φ n) (Φ n)) atTop
      (𝓝 (∫ p, kern a (p.1 - p.2) * B (idx N p.1) (idx N p.2) ∂(volI.prod volI))) := by
    have e : ∀ n, SpaceTimePositivity.stForm a Γ (Φ n) (Φ n) =
        ∫ p, kern a (p.1 - p.2) * ∑ i, ∑ j, χ n i p.1 * χ n j p.2 * B i j ∂(volI.prod volI) :=
      fun n => by unfold SpaceTimePositivity.stForm; simp_rw [hpair n]
    simp_rw [e]
    refine tendsto_integral_of_dominated_convergence (fun p => kern a (p.1 - p.2) * Bs)
      (fun n => ?_) (hkint.mul_const _) (fun n => ae_of_all _ fun p => ?_) ?_
    · refine (hkm.mul (Continuous.measurable ?_)).aestronglyMeasurable
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (((hχc n i).comp continuous_fst).mul ((hχc n j).comp continuous_snd)).mul continuous_const
    · rw [norm_mul, Real.norm_of_nonneg (kern_nonneg _ _)]
      refine mul_le_mul_of_nonneg_left ?_ (kern_nonneg _ _)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (hχ0 n i _), Real.norm_of_nonneg (hχ0 n j _),
        Real.norm_of_nonneg (hB0 i j)]
      calc χ n i p.1 * χ n j p.2 * B i j ≤ 1 * 1 * B i j :=
            mul_le_mul_of_nonneg_right (mul_le_mul (hχ1 n i _) (hχ1 n j _) (hχ0 n j _)
              zero_le_one) (hB0 i j)
        _ = B i j := by ring
    · filter_upwards [OccupationPhysicalClass.ae_prod_both (hIoo.and hoff)] with p hp
      have hcol : ∑ i, ∑ j, cellInd N i p.1 * cellInd N j p.2 * B i j =
          B (idx N p.1) (idx N p.2) := by
        have e1 : ∀ i, ∑ j, cellInd N i p.1 * cellInd N j p.2 * B i j =
            cellInd N i p.1 * B i (idx N p.2) := by
          intro i
          rw [← sum_cellInd hp.2.1 hp.2.2 (fun j => B i j), Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        simp_rw [e1]
        exact sum_cellInd hp.1.1 hp.1.2 (fun i => B i (idx N p.2))
      rw [← hcol]
      refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        ?_)
      exact ((hχlim i p.1).mul (hχlim j p.2)).mul tendsto_const_nhds
  -- the limit of the right side is `A(g)`
  have hA : A a Γ (stepG N f) =
      ∫ p, kern a (p.1 - p.2) * B (idx N p.1) (idx N p.2) ∂(volI.prod volI) := by
    have hsqP : ∀ i j, sqPair Γ (f i) (f j) = ENNReal.ofReal (B i j) := fun i j =>
      (SpatialStaticControls.pairing_eq_spatialPair (hsq i) (hsqs i) (fun x => sq_nonneg _)
        (hsq j) (hsqs j) (fun x => sq_nonneg _)).2.1
    have hnn : ∀ p : ℝ × ℝ, 0 ≤ kern a (p.1 - p.2) * B (idx N p.1) (idx N p.2) := fun p =>
      mul_nonneg (kern_nonneg _ _) (hB0 _ _)
    have hint : Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2) * B (idx N p.1) (idx N p.2))
        (volI.prod volI) := by
      refine (hkint.mul_const Bs).mono' (hkm.mul hBidx).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_of_nonneg (hnn p)]
      exact mul_le_mul_of_nonneg_left (hBle p) (kern_nonneg _ _)
    have hAr : Araw a Γ (stepG N f) = ∫⁻ p, ENNReal.ofReal (kern a (p.1 - p.2) *
        B (idx N p.1) (idx N p.2)) ∂(volI.prod volI) := by
      have hmE : Measurable fun p : ℝ × ℝ =>
          ENNReal.ofReal (kern a (p.1 - p.2) * B (idx N p.1) (idx N p.2)) :=
        ENNReal.measurable_ofReal.comp (hkm.mul hBidx)
      rw [lintegral_prod _ hmE.aemeasurable]
      unfold Araw stepG
      refine lintegral_congr fun s => lintegral_congr fun t => ?_
      rw [hsqP, ← ENNReal.ofReal_mul (kern_nonneg _ _)]
    unfold A
    rw [hAr, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn),
      ENNReal.toReal_ofReal (integral_nonneg hnn)]
  -- conclusion
  rw [← hP, hA]
  refine le_of_tendsto_of_tendsto' hLlim
    ((tendsto_const_nhds.mul hSlim).sqrt) fun n => ?_
  rw [← hLn n]
  exact hCS n

/-! ### `L:occupation-rayleigh-selection` -/

/-- **`L:occupation-rayleigh-selection`** (`integrated_occupation_ceiling.tex` lines 149-157,
proof 159-193, at a284420), under the section's standing assumptions (lines 4-21: `H:homog`
with `a = α₀`, `Γ ≠ 0`): for `Ψ ∈ C_pos` and `ε > 0` there is a field `g_ε` of `𝒪`
(`IsOccField`) with `I_Ψ² + T(g_ε) ≤ √(v_Ψ A(g_ε)) + ε` (`E:occupation-rayleigh-selection`),
`A` the ORIGINAL-kernel form of `RawOccupationEnergy`.  The field is a finite-cell field
`g_s = f_j` on the `j`-th of `N+1` equal cells, with real unit tests `f_j`.
Route differences (decision 2 of wave L9): finitely many equal time cells, with near-optimal
unit tests at the nodes (`OccupationCeilingFinite.exists_unitTest_gt`) and the uniform
Lipschitz bounds in `s` of `∫ h_s f²` (`L:variational-global-mean`) and of `λ_s²`
(`P:variational-unmasked-rate`), instead of the TeX's countable first-index Borel selection
over a dense sequence; the bound `∫∫ h g² ≤ √(v_Ψ A(g))` is `step_mean_le_sqrt` instead of
`L:occupation-raw-square`; `I_Ψ² ≤ ∫_0^1 λ_s² ds` is proved by Jensen (the TeX's time
Cauchy-Schwarz, lines 188-189).  Narrower as recorded in the module doc: `𝒪` is modelled by
`IsOccField` (the selected finite-cell field is a finite simple field of unit tests). -/
theorem occupation_rayleigh_selection_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG ∧
      integratedRate a Γ Ψ ^ 2 + T DG ≤ Real.sqrt (rawCost a Γ Ψ * A a Γ G) + ε := by
  have := hH.Γ_radon
  obtain ⟨ε0, M, C, -, -, hC, hbd, -, hR, hsupLip, -, hint, -, -⟩ :=
    VariationalRate.variational_unmasked_rate_paper hH hΓ0 hΨ
  obtain ⟨-, CΨ, -, hCΨ, -, -, hbd', hlipx, hcont, hpot⟩ :=
    VariationalMean.variational_global_mean_paper hH hΓ0 hΨ
  have : IsProbabilityMeasure volI := ⟨by simp⟩
  set L : ℝ → ℝ := fun s => sSup (rayleighSet (mean a Γ Ψ s)) with hLdef
  set m : (Rd d → ℝ) → ℝ → ℝ := fun g s => ∫ x, mean a Γ Ψ s x * g x ^ 2 with hmdef
  have hL2 : ∀ g : Rd d → ℝ, IsUnitTest g → MemLp g 2 volume := fun g hg =>
    VariationalFloor.memLp_test ⟨hg.1, hg.2.1⟩
  have hmlip : ∀ g : Rd d → ℝ, IsUnitTest g → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |m g s - m g t| ≤ CΨ * |s - t| := by
    intro g hg s hs t ht
    have hsqt := SpatialFourLinear.isTest_sq (φ := g) ⟨hg.1, hg.2.1⟩
    have hsq : Integrable (fun x => g x ^ 2) volume :=
      hsqt.1.continuous.integrable_of_hasCompactSupport hsqt.2
    have e : m g s - m g t = ∫ x, (mean a Γ Ψ s x - mean a Γ Ψ t x) * g x ^ 2 := by
      simp only [hmdef]
      rw [← integral_sub (hpot s hs g (hL2 g hg)) (hpot t ht g (hL2 g hg))]
      congr 1; funext x; ring
    rw [e, ← Real.norm_eq_abs]
    calc _ ≤ ∫ x, CΨ * |s - t| * g x ^ 2 :=
          norm_integral_le_of_norm_le (hsq.const_mul _) (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (g x))]
            exact mul_le_mul_of_nonneg_right (hlipx s hs t ht x) (sq_nonneg _))
      _ = CΨ * |s - t| := by rw [integral_const_mul, hg.2.2, mul_one]
  have hLcont : ContinuousOn L (Icc 0 1) := OccupationCeilingFinite.continuousOn_of_lip hC hsupLip
  -- the cell width
  set K := C + CΨ with hK
  have hK0 : 0 ≤ K := by positivity
  set δ := ε / (4 * (K + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have h2Kδ : 2 * (K * δ) ≤ ε / 2 := by
    rw [hδdef, show 2 * (K * (ε / (4 * (K + 1)))) = ε / 2 * (K / (K + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hcell : 1 / ((N : ℝ) + 1) ≤ δ := by
    rw [div_le_iff₀ hN1]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  -- near-optimal unit tests at the nodes
  set c : Fin (N + 1) → ℝ := fun j => ((j : ℕ) : ℝ) / ((N : ℝ) + 1) with hcdef
  have hc : ∀ j, c j ∈ Icc (0 : ℝ) 1 := by
    intro j
    refine ⟨by positivity, ?_⟩
    rw [hcdef, div_le_one hN1]
    have : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 j.2
    linarith
  have hsel : ∀ j, ∃ g, IsUnitTest g ∧ L (c j) - ε / 2 < m g (c j) - gradEnergy g := fun j =>
    OccupationCeilingFinite.exists_unitTest_gt (hcont _ (hc j)) (fun x => (hbd _ (hc j) x).1)
      (fun x => (hbd _ (hc j) x).2) (hR _ (hc j)).1 (by linarith)
  choose f hfU hfv using hsel
  obtain ⟨hO, hT⟩ := stepField_isOcc hfU
  refine ⟨stepG N f, stepDG N f, hO, ?_⟩
  -- the pointwise near-Rayleigh inequality
  have hkey : ∀ s ∈ Icc (0 : ℝ) 1,
      L s - ε ≤ m (f (idx N s)) s - gradEnergy (f (idx N s)) := by
    intro s hs
    set j := idx N s
    have hcl : |s - c j| ≤ δ := (idx_close hs).trans hcell
    have h2 := abs_le.mp (hmlip (f j) (hfU j) s hs (c j) (hc j))
    have h3 := abs_le.mp (hsupLip s hs (c j) (hc j))
    have h4 := hfv j
    have hCδ : C * |s - c j| ≤ C * δ := mul_le_mul_of_nonneg_left hcl hC
    have hCΨδ : CΨ * |s - c j| ≤ CΨ * δ := mul_le_mul_of_nonneg_left hcl hCΨ
    have hKδ : C * δ + CΨ * δ = K * δ := by rw [hK]; ring
    simp only [hLdef] at h3 h4 ⊢
    linarith [h2.1, h2.2, h3.1, h3.2]
  -- integrability of the three time integrands
  have hmeas_m : AEStronglyMeasurable (fun s => m (f (idx N s)) s) volI := by
    have e : (fun s => m (f (idx N s)) s) =
        fun s => ∑ j, {s | idx N s = j}.indicator (fun s => m (f j) s) s := by
      funext s
      rw [Finset.sum_eq_single (idx N s)]
      · exact (indicator_of_mem (show s ∈ {s | idx N s = idx N s} from rfl) _).symm
      · intro j _ hj
        exact indicator_of_notMem (show s ∉ {s | idx N s = j} from fun h => hj h.symm) _
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [e]
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    refine AEStronglyMeasurable.indicator ?_ ((idx_measurable N) (measurableSet_singleton j))
    exact ((OccupationCeilingFinite.continuousOn_of_lip hCΨ (hmlip _ (hfU j))).mono
      Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hIm : Integrable (fun s => m (f (idx N s)) s) volI := by
    refine (integrable_const M).mono' hmeas_m ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hb := mean_pair_bound (hbd s (Ioo_subset_Icc_self hs)) (hfU (idx N s))
      (hpot s (Ioo_subset_Icc_self hs) _ (hL2 _ (hfU _)))
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2
  have hIb : Integrable (fun s => gradEnergy (f (idx N s))) volI := by
    refine (integrable_const (∑ j, gradEnergy (f j))).mono'
      ((measurable_of_finite (fun j => gradEnergy (f j))).comp
        (idx_measurable N)).aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_of_nonneg (SpatialFourierBound.gradEnergy_nonneg _)]
    exact Finset.single_le_sum (fun j _ => SpatialFourierBound.gradEnergy_nonneg _)
      (Finset.mem_univ _)
  have hIL : IntegrableOn L (Ioo 0 1) := hLcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- Jensen: `I_Ψ² ≤ ∫ λ_s²`
  have hI2 : integratedRate a Γ Ψ ^ 2 ≤ ∫ s in Ioo (0 : ℝ) 1, L s := by
    have heq : EqOn (fun s => rate a Γ Ψ s ^ 2) L (Ioo 0 1) := fun s hs =>
      (hR s (Ioo_subset_Icc_self hs)).2.2.2.2.1
    have hsq : IntegrableOn (fun s => rate a Γ Ψ s ^ 2) (Ioo 0 1) :=
      hIL.congr_fun (fun s hs => (heq hs).symm) measurableSet_Ioo
    have hj := (convexOn_pow 2).map_integral_le (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (continuous_pow 2).continuousOn isClosed_Ici
      (ae_of_all _ fun s => (Real.sqrt_nonneg _ : (0 : ℝ) ≤ rate a Γ Ψ s)) hint hsq
    calc integratedRate a Γ Ψ ^ 2 ≤ ∫ s in Ioo (0 : ℝ) 1, rate a Γ Ψ s ^ 2 := hj
      _ = _ := setIntegral_congr_fun measurableSet_Ioo heq
  -- integrate the near-Rayleigh inequality
  have hint2 : (∫ s in Ioo (0 : ℝ) 1, L s) - ε ≤
      (∫ s, m (f (idx N s)) s ∂volI) - T (stepDG N f) := by
    have hvol : (volume : Measure ℝ).real (Ioo 0 1) = 1 := by simp
    rw [hT, ← integral_sub hIm hIb]
    calc (∫ s in Ioo (0 : ℝ) 1, L s) - ε = ∫ s in Ioo (0 : ℝ) 1, (L s - ε) := by
          rw [integral_sub hIL (continuousOn_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self),
            setIntegral_const, hvol, one_smul]
      _ ≤ _ := by
          refine setIntegral_mono_on (hIL.sub (integrableOn_const (by simp) (by simp)))
            (hIm.sub hIb) measurableSet_Ioo fun s hs => hkey s (Ioo_subset_Icc_self hs)
  have hCS := step_mean_le_sqrt hH hΓ0 hΨ hfU
  have hP : ∫ s, m (f (idx N s)) s ∂volI =
      ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ s x * stepG N f s x ^ 2 := rfl
  rw [hP] at hint2
  linarith

/-! ### `T:intrinsic-occupation-ceiling` -/

/-- Auxiliary to the Lean proof route: a field of `𝒪` has `A(g) ≤ C_occ T(g)^{α/2}` when the
ratio set is bounded above (`d ≥ 1`, so `T(g) > 0`). -/
theorem A_le_Cocc {a alpha : ℝ} {Γ : Measure (Rd d)} (hd : 0 < d)
    (hbdd : BddAbove (ratioSet a alpha Γ)) {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d}
    (hO : IsOccField G DG) : A a Γ G ≤ Cocc a alpha Γ * T DG ^ (alpha / 2) := by
  have hTp := Real.rpow_pos_of_pos (RawOccupationEnergy.T_pos hd hO) (alpha / 2)
  have := le_csSup hbdd (⟨G, DG, hO, rfl⟩ : A a Γ G / T DG ^ (alpha / 2) ∈ ratioSet a alpha Γ)
  rwa [div_le_iff₀ hTp] at this

/-- The first scalar maximum of the proof of `T:intrinsic-occupation-ceiling` (TeX lines
223-234) with the exact `C_occ`: under the standing assumptions, every `Ψ ∈ C_pos` satisfies
`I_Ψ² ≤ (q/4)(α/4)^{α/q} (v_Ψ C_occ)^{2/q}`, `q = 4 - α`, i.e. `I_Ψ ≤ D v_Ψ^{1/q}` with
`D = √(q/4)(α/4)^{α/(2q)} C_occ^{1/q}`.  Route as in the TeX: the selection lemma, the ratio
bound `A(g) ≤ C_occ T(g)^{α/2}`, the scalar maximum over `T ≥ 0`
(`OccupationCeilingFinite.young_quarter`), then `ε → 0`. -/
theorem integratedRate_sq_le_Cocc {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    integratedRate a Γ Ψ ^ 2 ≤ (4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha)) *
      (rawCost a Γ Ψ * Cocc a alpha Γ) ^ (2 / (4 - alpha)) := by
  have := hH.Γ_radon
  obtain ⟨hd, ha0, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  obtain ⟨-, hbdd, hCpos, -⟩ := RawOccupationEnergy.raw_occupation_energy_paper hH hΓ0
  have hv : 0 < rawCost a Γ Ψ :=
    ((VariationalRate.variational_positive_scores_paper hH hΓ0).2.1 Ψ hΨ).2.2.2.2
  set X := rawCost a Γ Ψ * Cocc a alpha Γ with hXdef
  have hX : 0 ≤ X := mul_nonneg hv.le hCpos.le
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨G, DG, hO, hsel⟩ := occupation_rayleigh_selection_paper hH hΓ0 hΨ hε
  have hT0 : 0 ≤ T DG := ENNReal.toReal_nonneg
  have hAle := A_le_Cocc hd hbdd hO
  have hsq : Real.sqrt (rawCost a Γ Ψ * A a Γ G) ≤ Real.sqrt X * T DG ^ (alpha / 4) := by
    calc Real.sqrt (rawCost a Γ Ψ * A a Γ G)
        ≤ Real.sqrt (rawCost a Γ Ψ * (Cocc a alpha Γ * T DG ^ (alpha / 2))) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hAle hv.le)
      _ = Real.sqrt X * T DG ^ (alpha / 4) := by
          rw [show rawCost a Γ Ψ * (Cocc a alpha Γ * T DG ^ (alpha / 2)) =
            X * T DG ^ (alpha / 2) by rw [hXdef]; ring, Real.sqrt_mul hX,
            Real.sqrt_eq_rpow (T DG ^ (alpha / 2)), ← Real.rpow_mul hT0]
          ring_nf
  have hY := OccupationCeilingFinite.young_quarter ha0 (by linarith) hX hT0
  linarith

/-- The ceiling for one control (TeX lines 235-243) with the exact `C_occ`: under the standing
assumptions, for `c > 0` and `Ψ ∈ C_pos`, `c I_Ψ - v_Ψ/2 ≤ U_c` with
`U_c = c^m k [α^{α/2} C_occ/(8 q^{q/2})]^{1/k}` (`SpatialBracket.ceilingValue α c C_occ`).
Route: `integratedRate_sq_le_Cocc`, the second scalar maximum
(`OccupationCeilingFinite.young_q`) and the positive-power algebra
(`OccupationCeilingFinite.ceilingValue_eq`), as in `OccupationCeilingFinite.score_le_ceiling`. -/
theorem score_le_ceiling_Cocc {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) {c : ℝ} (hc : 0 < c)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    c * integratedRate a Γ Ψ - rawCost a Γ Ψ / 2 ≤
      SpatialBracket.ceilingValue alpha c (Cocc a alpha Γ) := by
  have := hH.Γ_radon
  obtain ⟨-, ha0, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  obtain ⟨-, -, hC, -⟩ := RawOccupationEnergy.raw_occupation_energy_paper hH hΓ0
  have hv : 0 < rawCost a Γ Ψ :=
    ((VariationalRate.variational_positive_scores_paper hH hΓ0).2.1 Ψ hΨ).2.2.2.2
  set C := Cocc a alpha Γ with hCdef
  have hq : 0 < 4 - alpha := by linarith
  have hP : 0 < (4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha)) := by positivity
  have hsq := integratedRate_sq_le_Cocc hH hΓ0 hΨ
  rw [← hCdef] at hsq
  have hIle : integratedRate a Γ Ψ ≤ Real.sqrt ((4 - alpha) / 4 *
      (alpha / 4) ^ (alpha / (4 - alpha))) * C ^ (1 / (4 - alpha)) *
      rawCost a Γ Ψ ^ (1 / (4 - alpha)) := by
    have h1 := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
    rw [Real.sqrt_mul hP.le, Real.sqrt_eq_rpow ((rawCost a Γ Ψ * C) ^ _),
      ← Real.rpow_mul (mul_nonneg hv.le hC.le), Real.mul_rpow hv.le hC.le] at h1
    rw [show 2 / (4 - alpha) * (1 / 2) = 1 / (4 - alpha) by field_simp] at h1
    linarith
  have hY := OccupationCeilingFinite.young_q (alpha := alpha) (by linarith)
    (E := c * Real.sqrt ((4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha))) *
      C ^ (1 / (4 - alpha))) (by positivity) hv.le
  rw [OccupationCeilingFinite.ceilingValue_eq ha0 ha2 hC hc] at hY
  have e : OccupationCeilingFinite.ceilingValue alpha c C = SpatialBracket.ceilingValue alpha c C :=
    rfl
  rw [← e]
  nlinarith [mul_le_mul_of_nonneg_left hIle hc.le]

/-- **`T:intrinsic-occupation-ceiling`** (`integrated_occupation_ceiling.tex` lines 205-220,
proof 222-250, at a284420) with the EXACT constant `C_occ` (`RawOccupationEnergy.Cocc`), both
forms, for the variational values `S_c^pos = sSup (VariationalRate.scoreSet α₀ Γ c)`, under the
section's standing assumptions (lines 4-21: `H:homog` with `a = α₀`, `Γ ≠ 0`).  For every
`c > 0`: the value set is nonempty and bounded above, every `Ψ ∈ C_pos` has
`c I_Ψ - v_Ψ/2 ≤ U_c`, `S_c^pos ≤ U_c = c^m k [α^{α/2} C_occ/(8 q^{q/2})]^{1/k}`
(`E:occupation-score-ceiling`), and for every `ζ > 0`,
`U_c = c^m (2ζ)^{α/(2k)} F_0(𝓔_ζ^𝒪)` (`q = 4-α`, `k = 3-α`, `m = q/k`; `F_0` is
`SpatialFourLinear.F0`, `𝓔_ζ^𝒪` is `RawOccupationEnergy.EO`).
Narrower than the TeX (recorded): the moment sentence `C_2(Γ,a) ≤ U_2` (line 217) is not
formalized (it needs `T:intrinsic-second-moment`, foundation D1); the class `𝒪` is modelled by
joint representatives (`IsOccField`), as in `P:raw-occupation-energy`.  The coefficient range
`c > 0` is that of `P:variational-positive-scores` (`integrated_unmasked_variational.tex`
line 272), where `S_c^pos` is defined.  Route difference: the selection lemma by finite cells
(`occupation_rayleigh_selection_paper`); the second form from `E:raw-occupation-energy`
(`RawOccupationEnergy.raw_occupation_energy_paper`) and
`SpatialBracket.ceilingValue_eq_zeta`.  No input is supplied (`S1Bdd` is not assumed). -/
theorem intrinsic_occupation_ceiling_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) :
    ∀ c : ℝ, 0 < c →
      (scoreSet a Γ c).Nonempty ∧ BddAbove (scoreSet a Γ c) ∧
      (∀ Ψ ∈ CPos d, c * integratedRate a Γ Ψ - rawCost a Γ Ψ / 2 ≤
        SpatialBracket.ceilingValue alpha c (Cocc a alpha Γ)) ∧
      sSup (scoreSet a Γ c) ≤ SpatialBracket.ceilingValue alpha c (Cocc a alpha Γ) ∧
      ∀ ζ : ℝ, 0 < ζ → SpatialBracket.ceilingValue alpha c (Cocc a alpha Γ) =
        c ^ ((4 - alpha) / (3 - alpha)) * (2 * ζ) ^ (alpha / (2 * (3 - alpha))) *
          SpatialFourLinear.F0 alpha (EO a Γ ζ) := by
  intro c hc
  obtain ⟨-, ha0, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  obtain ⟨-, -, hC, -, -, hE⟩ := RawOccupationEnergy.raw_occupation_energy_paper hH hΓ0
  have hne := (VariationalRate.variational_positive_scores_paper hH hΓ0).1 c
  have hpt := fun Ψ (hΨ : Ψ ∈ CPos d) => score_le_ceiling_Cocc hH hΓ0 hc hΨ
  have hb : ∀ y ∈ scoreSet a Γ c, y ≤ SpatialBracket.ceilingValue alpha c (Cocc a alpha Γ) := by
    rintro _ ⟨Ψ, hΨ, rfl⟩
    exact hpt Ψ hΨ
  refine ⟨hne, ⟨_, hb⟩, hpt, csSup_le hne hb, fun ζ hζ => ?_⟩
  rw [(hE ζ hζ).2.2.1]
  exact SpatialBracket.ceilingValue_eq_zeta ha0 ha2 hC.le hζ

/-- **The comparison of `C:intrinsic-spatial-bracket`** (`integrated_occupation_ceiling.tex`
lines 261-265, proof 275-290, at a284420), for the variational value `S_2^pos`, with the exact
`𝓔_{1/2}^𝒪`: under the section's standing assumptions (`H:homog` with `a = α₀`, `Γ ≠ 0`),
the value set at `c = 2` is nonempty and bounded above, and
`S_2^pos ≤ 2^m F_0(𝓔_{1/2}^𝒪) < 2^m F_a(𝓔_{1/2}^𝒪)` (`F_a = SpatialBracket.Fb α a`).
Narrower than the TeX (recorded): stated for `S_2^pos`, not `C_2(Γ,a)` (the identification
`C_2 = S_2^pos` is `T:intrinsic-second-moment`, foundation D1); the bracket
`E:intrinsic-spatial-bracket` itself is `SpatialBracket.intrinsic_spatial_bracket_paper`.
Route as in the TeX: the ceiling at `ζ = 1/2` and `F_0 < F_a` (`Δ > 0`). -/
theorem intrinsic_spatial_comparison_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) :
    (scoreSet a Γ 2).Nonempty ∧ BddAbove (scoreSet a Γ 2) ∧
      sSup (scoreSet a Γ 2) ≤
        2 ^ ((4 - alpha) / (3 - alpha)) * SpatialFourLinear.F0 alpha (EO a Γ (1 / 2)) ∧
      2 ^ ((4 - alpha) / (3 - alpha)) * SpatialFourLinear.F0 alpha (EO a Γ (1 / 2)) <
        2 ^ ((4 - alpha) / (3 - alpha)) * SpatialBracket.Fb alpha a (EO a Γ (1 / 2)) := by
  obtain ⟨-, ha0, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  obtain ⟨-, -, -, -, -, hE⟩ := RawOccupationEnergy.raw_occupation_energy_paper hH hΓ0
  obtain ⟨hne, hbdd, -, hS, hU⟩ := intrinsic_occupation_ceiling_paper hH hΓ0 2 two_pos
  have hEpos := (hE (1 / 2) (by norm_num)).2.2.2.2.1
  have hU2 := hU (1 / 2) (by norm_num)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.one_rpow, mul_one] at hU2
  refine ⟨hne, hbdd, hU2 ▸ hS, ?_⟩
  have h2 : 0 < 4 - alpha - 2 * a := by linarith [hH.alpha0_lt_one]
  exact mul_lt_mul_of_pos_left (SpatialBracket.F0_lt_Fa ha2 hH.alpha0_pos h2 hEpos)
    (Real.rpow_pos_of_pos two_pos _)

end StratonovichHAMSecondMoment.OccupationCeilingExact
