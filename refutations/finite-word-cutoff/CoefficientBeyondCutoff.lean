/-
Refutation for the count condition `r_i ≤ N_i` in the identification of the
selected coefficients (main TeX lines 4163-4170 at 39f2597a: "truncate the Hermite
degree of color `i` at `N_i = 2k_i`. A word contributing to `U_r` has `r_i ≤ 2k_i`
insertions"), package theorem
`StratonovichHAMSecondMoment.FiniteWordCutoff.coef_cutoff_eq` and the supplied input
`DuhamelWords`.

Wrong variant: under the Duhamel word expansion the cutoff coefficient is the uncut
coefficient at every cutoff.  Counterexample (a genuine instance of `DuhamelWords`,
so the input is not vacuous): one color with one mode, spatial space `ℂ`, `σ = 1`,
`B = id`, the frame swapping the phase components (also as the first free factor
`F_0`), initial phase `(0, 1)`, one word `g g` with the Dirac measure (`r = 2`).
The uncut coefficient has first component `g² ⊗ 1 = √2 h_2 + h_0`, coefficient
`√2` at degree 2; at cutoff `N = 1`
the cutoff coefficient vanishes at degree 2.  `coefficient_beyond_cutoff_contrast` is
the package identification at `N = 2` for the same instance.  No junk-value
reliance (the Dirac integral is the true value).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FiniteWordCutoff

set_option autoImplicit false

namespace Refutations.FiniteWordCutoff.BeyondCutoff

open MeasureTheory
open StratonovichHAMSecondMoment.FiniteWordCutoff StratonovichHAMSecondMoment.FixedSplit
open StratonovichHAMSecondMoment.HermiteFock
open StratonovichHAMSecondMoment.GaussianHermite (unitIdx)

/-- The single color of the example. -/
abbrev col1 : Fin 1 → Unit := fun _ => ()

/-- The spatial insertion operators of the example (identities). -/
noncomputable abbrev K1 : Fin 1 → ℂ →L[ℂ] ℂ := fun _ => ContinuousLinearMap.id ℂ ℂ

/-- The noise amplitude `σ = 1`. -/
abbrev σ1 : Unit → ℝ := fun _ => 1

/-- The frame swapping the two phase components. -/
noncomputable abbrev Fsw : Unit → ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  fun _ => (ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)

/-- The word `g g`. -/
abbrev w2 : List (Unit × Unit) := [((), ()), ((), ())]

/-- The word data: one word, the Dirac measure on `Unit`. -/
abbrev A1 : Finset Unit := {()}

/-- The Dirac measure. -/
noncomputable abbrev μ1 : Unit → Measure Unit := fun _ => Measure.dirac ()

/-- The constant word map (first frame label `()`, word `g g`). -/
abbrev ω1 : Unit → Unit → Unit × List (Unit × Unit) := fun _ _ => ((), w2)

/-- The uncut coefficient `U_r v` of the instance. -/
noncomputable abbrev U1 : FullPhase ℂ 1 :=
  wordCoefP A1 μ1 ω1 (fun x => raw (insP col1 σ1 K1) (fun b => frameP (Fsw b))
    (frameP (Fsw x.1) (vacP 0 1)) x.2)

/-- The cutoff coefficient of the instance at cutoff `N`. -/
noncomputable abbrev c1 (N : Unit → ℕ) : PhaseSp ℂ col1 N :=
  cutWordC col1 N σ1 K1 Fsw (startC (Fsw ()) 0 1) w2

/-- The constant multi-index of degree `n`. -/
abbrev ix (n : ℕ) : Fin 1 → ℕ := fun _ => n

theorem ix_sub (n : ℕ) : ix n - unitIdx 0 = ix (n - 1) := by
  funext j; fin_cases j; simp [ix]

theorem ix_add (n : ℕ) : ix n + unitIdx 0 = ix (n + 1) := by
  funext j; fin_cases j; simp [ix]

theorem ix_eq_zero (n : ℕ) : ix n = 0 ↔ n = 0 := by
  constructor
  · intro h; have := congrFun h 0; simpa [ix] using this
  · rintro rfl; rfl

theorem field_ix (v : (Fin 1 → ℕ) → ℂ) (n : ℕ) :
    field col1 K1 () v (ix n) =
      (Real.sqrt n : ℂ) * v (ix (n - 1)) + (Real.sqrt (n + 1) : ℂ) * v (ix (n + 1)) := by
  simp [field, gmul, cre, ann, K1]
  rw [ix_sub, ix_add]

theorem field_vac (n : ℕ) : field col1 K1 () (vac 1) (ix n) = if n = 1 then 1 else 0 := by
  rw [field_ix]
  simp only [vac, ix_eq_zero]
  rcases n with _ | _ | n <;> simp

theorem field_field_two : field col1 K1 () (field col1 K1 () (vac 1)) (ix 2) = Real.sqrt 2 := by
  rw [field_ix, field_vac, field_vac]
  norm_num

theorem not_mem_cut : ix 2 ∉ cutIdx col1 (fun _ => 1) := by
  rw [mem_cutIdx]
  intro hk
  have := hk ()
  simp [colorDeg, ix] at this

/-- `DuhamelWords` holds for the instance at every cutoff. -/
theorem duhamel (N : Unit → ℕ) :
    DuhamelWords col1 N σ1 K1 Fsw 0 1 A1 μ1 ω1 (fun _ => 2) U1 (c1 N) := by
  refine ⟨fun a _ t => ?_, rfl, ?_⟩
  · funext i; simp [counts, bump]
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [wordCoefP]

/-- The uncut coefficient at degree 2 (first component) is `√2`. -/
theorem U1_two : U1.1 (ix 2) = Real.sqrt 2 := by
  simp only [U1, wordCoefP, Finset.sum_singleton, μ1, integral_dirac]
  change (frameP (Fsw ()) (insP col1 σ1 K1 () (frameP (Fsw ()) (insP col1 σ1 K1 ()
    (frameP (Fsw ()) (vacP 0 1)))))).1 (ix 2) = _
  simp only [frameP, insP, Fsw, vacP, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', σ1]
  simp only [Complex.ofReal_one, one_smul]
  exact field_field_two

/-- Beyond the cutoff (`r = 2 > 1 = N`) the cutoff coefficient is not the uncut one,
although the Duhamel word expansion holds. -/
theorem coefficient_beyond_cutoff_refuted :
    ¬ (∀ (N : Unit → ℕ) (c : PhaseSp ℂ col1 N),
        DuhamelWords col1 N σ1 K1 Fsw 0 1 A1 μ1 ω1 (fun _ => 2) U1 c → extP c = U1) := by
  intro hall
  have h := congrArg (fun x : FullPhase ℂ 1 => x.1 (ix 2)) (hall _ _ (duhamel (fun _ => 1)))
  rw [U1_two, c1, extP_cutWordC] at h
  change (frameP (Fsw ()) (truncP col1 (fun _ => 1) _)).1 (ix 2) = _ at h
  simp [frameP, truncP, truncN, not_mem_cut] at h
  have : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  exact this h.symm

/-- The package identification at `N = 2 = r` for the same instance. -/
theorem coefficient_beyond_cutoff_contrast : extP (c1 (fun _ => 2)) = U1 :=
  coef_cutoff_eq col1 (fun _ => 2) σ1 K1 Fsw 0 1 A1 μ1 ω1 (fun _ => 2) U1 _
    (duhamel _) fun _ => le_rfl

end Refutations.FiniteWordCutoff.BeyondCutoff
