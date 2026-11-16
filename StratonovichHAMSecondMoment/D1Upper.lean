module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`P:d1-upper` (One-dimensional upper bound) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision 39f2597a (wave L13
item D2): statement at main TeX lines 5454-5468 (`E:d1-coefficient`, lines
5458-5462, and `E:d1-upper`, lines 5464-5467), proof at lines 5478-5550; the
covariances `E:d1-covariances` (lines 5317-5322), the constants `b`, `q`, `β`,
`Z`, `K_sp` of `E:d1-constants` (lines 5323-5332), the standing `0 < α₀ < 1`
(line 5315) and the coefficients `A_k(t)` (lines 5446-5451).

How the TeX's objects map to the model (`DiagramModel`, a registered model
choice; `L:d1-spatial` is `D1Spatial`):
* the smoothed mixed expectation `Σ_D E[X_m^{ε} X_{2k-m}^{ε}]` at spatial width
  `ε` is the model's diagram sum `Σ_{D ∈ Π_k} diagram (waveGreen 1) (covEps Γ ε)`,
  and the TeX's `A_k(t)` at width `ε` is `coeffA (waveGreen 1) (covEps Γ ε) α₀ k t`;
  the TeX's limit `A_k(t)` is `coeffALim 1 Γ α₀ k t` (the sum of the limits
  `diagramLim`), equal to `Σ_m E[X_m X_{2k-m}]` under `MixedMoment`
  (`DiagramModel.MixedMoment.coeffA_eq`).  The model keeps the exact time kernel
  (the TeX's temporal truncation `δ` is not needed: `ℝ≥0∞` integrals of the exact
  kernel are used directly) and one common noise width `ε` for all pairs;
* the Riesz case is `Γ = c|y|^{-α} dy` (`volume.withDensity (riesz c α)`), the
  white case `Γ = c δ₀` (`whiteCov c`), as in `D1Spatial`;
* `Z = 2/((1-α₀)(2-α₀))` is `Zc α₀`, `K_sp` is `D1Spatial.Ksp c α` (Riesz) or `c`
  (white), `b = 2 - α`, `q = 3 - α`, `β = 4 - α - α₀` (white: `α = 1`).

Formalized (all proved; the limit form and the moment display use the
supplied inputs named below):
* the dimension-free time facts are shared with `P:low-alpha-upper` in
  `TwoSimplexTime` (deduplicated at the L13 integration; D2 and D3 had proved
  them in parallel): on `[0,t]^m_< × [0,t]^n_<` the increments sum to at most
  `2t` (lines 5484-5485, `TwoSimplexTime.sum_incr_le`); the full symmetry of
  `F_k`, the `m! n!` symmetrization, the pair integral `Z t^{2-α₀}`
  (`TwoSimplexTime.lintegral_timeCov_square`, `pairInt_eq`), the cube integral
  of one pairing, the binomial identity `Σ_m 1/(m!(2k-m)!) = 2^{2k}/(2k)!`
  (line 5515, `TwoSimplexTime.sum_inv_factorial_gen`), `P_k = (2k)!/(2^k k!)`
  (`TwoSimplexTime.card_Pi2_eq`), and the generic count bound
  `TwoSimplexTime.coeffA_le`;
* `E:d1-time-symmetry` (lines 5503-5506), in the inequality form the proof
  uses: for every measurable `F` invariant under all permutations of the labels,
  `m! n! ∫_{[0,t]^m_< × [0,t]^n_<} F ≤ ∫_{[0,t]^{m+n}} F`
  (`card_mul_lintegral_twoSimplex_le`, by the pairwise disjointness of the
  `m! n!` chain-reordered simplices); the full symmetry of
  `F_k = Σ_{D ∈ Π_k} ∏_{(i,j) ∈ D} |s_i - s_j|^{-α₀}` (lines 5491-5494,
  `timeSum_comp_perm`: permutations biject `Π_k`), both from `TwoSimplexTime`;
* the cube integral of lines 5497-5499 on the closed cube, per pairing,
  `∫_{[0,t]^{2k}} ∏_{(i,j) ∈ D} |s_i - s_j|^{-α₀} = (Z t^{2-α₀})^k`
  (`lintegral_cube_timeWeight`, from the open-cube `TwoSimplexTime` version);
* the coefficient display at every width `ε > 0` (lines 5520-5528):
  `coeffA_riesz_le`, `coeffA_white_le` (the first inequality of
  `E:d1-coefficient`) and the second inequality `k! k^{bk} ≥ (k!)^q`
  (lines 5537-5538) in `coeffA_riesz_le_factorial`, `coeffA_white_le_factorial`;
  the generic core `coeffA_le_of_spatial` takes any spatial bound of the form
  `E:d1-spatial-max`;
* the limit `A_k(t)` (lines 5534-5537): `coeffALim_riesz_le`, `coeffALim_white_le`
  under the supplied input `DiagramLimits`;
* `E:d1-upper` (lines 5540-5549): `secondMoment_riesz_le`,
  `secondMoment_white_le` under the supplied input `MixedMoment`, via
  `SeriesType.seriesNu_summable_le` (the TeX's `ℓ^q` step);
* wrappers with the manuscript's hypotheses: `d1_upper_paper_riesz`,
  `d1_upper_paper_white`;
* the white case without `DiagramLimits` (L13 integration): `diagramLimits_white`
  proves `DiagramLimits 1 (whiteCov c) α₀ t` for `α₀ < 1` from
  `WhiteCollapse.tendsto_diagram_white` (every diagram, `Γ = δ₀`) and the scaling
  `diagram_const_mul` (`Γ = c δ₀` multiplies a diagram by `c^{#pairs}`), so
  `coeffALim_white_le'` and the wrapper `d1_upper_paper_white'` state the limit
  coefficient display for white noise with no supplied input.  The moment display
  still needs `MixedMoment` (its second clause is about the unconstructed `X`).

Supplied inputs (named):
* `DiagramLimits 1 Γ α₀ t` (defined here): every diagram converges as `ε ↓ 0`
  to `diagramLim` (the first clause of `MixedMoment`; part of
  `L:joint-fixed-order`, main TeX lines 1853-1966, which the TeX's own proof
  invokes at line 5534).  Without it `diagramLim` is an unspecified `limUnder`
  value.  TRUE under `H:homog`, by `L:joint-fixed-order`.
* `DiagramModel.MixedMoment` (the statement of `P:mixed`, D5): for the moment
  display, `E u² = Σ_k A_k(t)` with `A_k = Σ_m E[X_m X_{2k-m}]`.

Differences from the TeX's route (statements unchanged): the TeX states
`E:d1-time-symmetry` as an equality (ties of measure zero); only the inequality
`≤` is used and proved, which needs no null-set argument.  The measurability
hypothesis of `card_mul_lintegral_twoSimplex_le` is carried but unused since the
L13 integration (the shared proof needs none).  The temporal
truncation `δ` of the source is not used: the model's diagrams carry the exact
kernel `|s_i - s_j|^{-α₀}` in `ℝ≥0∞`.  The TeX's hypothesis `t > 0` is used; the
time integrals need only `α₀ < 1`, so `α₀ > 0` is carried but unused, and
`c > 0` is used only as `c ≥ 0`.

Category: narrower.  Whole on the model: the coefficient display at every
noise width `ε > 0`, uniformly in `ε` (both inequalities of `E:d1-coefficient`,
both covariance cases).  Inputs-supplied: the coefficient display for the limit
`A_k(t)` in the Riesz case (needs `DiagramLimits`, the limit existence of
`L:joint-fixed-order`; in the white case it is proved, `d1_upper_paper_white'`)
and in the TeX's form `Σ_m E[X_m X_{2k-m}]` (needs `MixedMoment`).  Narrower:
`E:d1-upper` is about `u`, which is not constructed (blocker D5); it is proved
for any random variable `u` satisfying `MixedMoment` (split modelled-object
rule).

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.D1Spatial
public import StratonovichHAMSecondMoment.TwoSimplexTime
public import StratonovichHAMSecondMoment.TimeSchur
public import StratonovichHAMSecondMoment.SeriesType
public import StratonovichHAMSecondMoment.WhiteCollapse

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Nat

namespace StratonovichHAMSecondMoment.D1Upper

open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open DiagramModel
open D1Spatial (Ksp)
open TwoSimplexTime (Zc Zc_pos)
open FiniteWick (pairings mem_pairings)
open HigherRieszTwo (riesz)
open WhiteModel (whiteCov)

/-! ### The constants -/
/-- `K_sp ≥ 0` in the Riesz case. -/
theorem Ksp_nonneg {c α : ℝ} (hc : 0 ≤ c) (hα1 : α < 1) : 0 ≤ Ksp c α := by
  unfold Ksp
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < 2 - α := by linarith
  positivity

/-! ### Symmetrization over the chain orders (`E:d1-time-symmetry`) -/

/-- **`E:d1-time-symmetry` in inequality form** (main TeX lines 5503-5506): for
a measurable `F ≥ 0` invariant under every permutation of the `m + n` labels,
`m! n! ∫_{[0,t]^m_< × [0,t]^n_<} F ≤ ∫_{[0,t]^{m+n}} F`.  Proof: the `m! n!`
chain reorderings of the simplices are pairwise disjoint subsets of the cube
(`TwoSimplexTime.chainPerms_disjoint`), and each has the same integral by the
permutation invariance of Lebesgue measure and of `F`
(`TwoSimplexTime.card_mul_setLIntegral_le`). -/
theorem card_mul_lintegral_twoSimplex_le {m n : ℕ} (t : ℝ) {F : (Fin (m + n) → ℝ) → ℝ≥0∞}
    (_hF : Measurable F) (hsym : ∀ (σ : Equiv.Perm (Fin (m + n))) (s : Fin (m + n) → ℝ),
      F (s ∘ σ) = F s) :
    ((m ! * n ! : ℕ) : ℝ≥0∞) * ∫⁻ s in twoSimplex m n t, F s ≤
      ∫⁻ s in Set.univ.pi (fun _ : Fin (m + n) => Icc 0 t), F s := by
  rw [← TwoSimplexTime.card_chainPerms]
  refine TwoSimplexTime.card_mul_setLIntegral_le (measurableSet_twoSimplex m n t) _
    (fun σ _ s => hsym σ s)
    (fun σ hσ τ hτ s h1 h2 => TwoSimplexTime.chainPerms_disjoint σ τ hσ hτ s h1 h2) ?_
  intro σ _ s hs j _
  have h := pos_of_mem_twoSimplex hs (σ.symm j)
  have h' := (hs (σ.symm j)).2
  simp only [Function.comp, Equiv.apply_symm_apply] at h h'
  exact ⟨h.le, h'.le⟩

/-- **The full symmetry of `F_k`** (main TeX lines 5491-5494): the sum over all
pairings of the temporal weights is invariant under every permutation of the
labels, since a permutation bijects `Π_k` (`TwoSimplexTime.sum_timeWeight_comp_perm`). -/
theorem timeSum_comp_perm (α₀ : ℝ) {m n : ℕ} (σ : Equiv.Perm (Fin (m + n)))
    (s : Fin (m + n) → ℝ) :
    ∑ D ∈ Pi2 m n, timeWeight α₀ D (s ∘ σ) = ∑ D ∈ Pi2 m n, timeWeight α₀ D s :=
  TwoSimplexTime.sum_timeWeight_comp_perm σ α₀ s

/-! ### The time integrals over the cube -/

/-- **The cube integral of one pairing** (main TeX lines 5497-5499, by the
disjoint endpoints): `∫_{[0,t]^{2k}} ∏_{(i,j) ∈ D} |s_i - s_j|^{-α₀} ds =
(Z t^{2-α₀})^k`.  From `TwoSimplexTime.lintegral_cube_timeWeight` (open cube) and
`TwoSimplexTime.pairInt_eq`; the closed and open cubes differ by a null set. -/
theorem lintegral_cube_timeWeight {a t : ℝ} (ha1 : a < 1) (ht : 0 ≤ t) {N k : ℕ}
    (hN : N = 2 * k) {D : Fin N → Fin N} (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) :
    ∫⁻ s in Set.univ.pi (fun _ : Fin N => Icc 0 t), timeWeight a D s =
      ENNReal.ofReal (Zc a * t ^ (2 - a)) ^ k := by
  have hae : (Set.univ.pi fun _ : Fin N => Ioo (0 : ℝ) t) =ᵐ[volume]
      Set.univ.pi fun _ : Fin N => Icc (0 : ℝ) t := by
    rw [volume_pi]; exact Measure.pi_Ioo_ae_eq_pi_Icc
  rw [← setLIntegral_congr hae]
  have h := TwoSimplexTime.lintegral_cube_timeWeight hD hN a t
  rw [TwoSimplexTime.cube, TwoSimplexTime.pairInt_eq ha1 ht] at h
  exact h

/-! ### Combinatorics -/

/-- The second inequality of `E:d1-coefficient` (main TeX lines 5537-5538):
`k! k^{bk} ≥ (k!)^{b+1}` for `b ≥ 0`, since `k! ≤ k^k`. -/
theorem factorial_rpow_le {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    (k ! : ℝ) ^ (b + 1) ≤ k ! * (k : ℝ) ^ (b * k) := by
  have hf : (0 : ℝ) < k ! := by positivity
  rw [Real.rpow_add hf, Real.rpow_one, mul_comm ((k ! : ℝ) ^ b)]
  gcongr
  calc (k ! : ℝ) ^ b ≤ ((k : ℝ) ^ k) ^ b :=
        Real.rpow_le_rpow hf.le (by exact_mod_cast Nat.factorial_le_pow k) hb
    _ = (k : ℝ) ^ (b * k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]

/-- Auxiliary: `Q/(k! k^{bk}) ≤ Q/(k!)^{b+1}` for `Q ≥ 0`. -/
theorem div_le_div_factorial {Q b : ℝ} (hQ : 0 ≤ Q) (hb : 0 ≤ b) (k : ℕ) :
    Q / (k ! * (k : ℝ) ^ (b * k)) ≤ Q / (k ! : ℝ) ^ (b + 1) :=
  div_le_div_of_nonneg_left hQ (Real.rpow_pos_of_pos (by positivity) _) (factorial_rpow_le hb k)

/-! ### The coefficient display at a positive width -/

/-- **The generic coefficient bound** (main TeX lines 5477-5528): if, for every
split and pairing of total order `2k`, the spatial part obeys a bound of the form
`E:d1-spatial-max`, `K^k t^{bk}/k^{bk}`, then
`A_k(t) ≤ (2ZK)^k t^{(b+2-α₀)k}/(k! k^{bk})` (the first inequality of
`E:d1-coefficient`, with `β = b + 2 - α₀`).  From the dimension-free
`TwoSimplexTime.coeffA_le` with `B = K^k t^{bk}/k^{bk}`. -/
theorem coeffA_le_of_spatial {d : ℕ} {G : ℝ → Measure (Rd d)} {γ : Rd d → ℝ≥0∞}
    {α₀ t K b : ℝ} (ha1 : α₀ < 1) (ht : 0 < t) (hK : 0 ≤ K) {k : ℕ} (hk : 1 ≤ k)
    (hsp : ∀ m ≤ 2 * k, ∀ D ∈ Pi2 m (2 * k - m), ∀ h : Fin (m + (2 * k - m)) → ℝ,
      (∀ i, 0 ≤ h i) → ∑ i, h i ≤ 2 * t →
        spatial G γ m D h ≤ ENNReal.ofReal (K ^ k * t ^ (b * k) / (k : ℝ) ^ (b * k))) :
    coeffA G γ α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * K) ^ k * t ^ ((b + (2 - α₀)) * k) /
        (k ! * (k : ℝ) ^ (b * k))) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hB : 0 ≤ K ^ k * t ^ (b * k) / (k : ℝ) ^ (b * k) :=
    div_nonneg (mul_nonneg (pow_nonneg hK _) (Real.rpow_nonneg ht.le _))
      (Real.rpow_nonneg hkpos.le _)
  refine (TwoSimplexTime.coeffA_le G γ ha1 k ht.le
    (ENNReal.ofReal (K ^ k * t ^ (b * k) / (k : ℝ) ^ (b * k))) ?_).trans (le_of_eq ?_)
  · intro m n hmn D hD h hpos hsum
    obtain rfl : n = 2 * k - m := by omega
    exact hsp m (by omega) D hD h (fun i => (hpos i).le) hsum
  · rw [← ENNReal.ofReal_mul hB]
    congr 1
    have ht' : t ^ ((b + (2 - α₀)) * k) = t ^ (b * k) * (t ^ (2 - α₀)) ^ k := by
      rw [add_mul, Real.rpow_add ht, ← Real.rpow_natCast (t ^ (2 - α₀)),
        ← Real.rpow_mul ht.le]
    rw [ht']
    have h2 : (0 : ℝ) < (k : ℝ) ^ (b * k) := Real.rpow_pos_of_pos hkpos _
    have h3 : (0 : ℝ) < k ! := by positivity
    field_simp
    ring

/-- **`E:d1-coefficient`, Riesz case, at every width** (main TeX lines
5458-5462 with the uniform bound of lines 5520-5528): for `0 < α < 1`,
`c ≥ 0`, `α₀ < 1`, `t > 0`, `k ≥ 1` and every noise width `ε > 0`,
`A_k^ε(t) ≤ (2ZK_sp)^k t^{βk}/(k! k^{bk})`, `β = 4 - α - α₀`, `b = 2 - α`. -/
theorem coeffA_riesz_le {c α α₀ t ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (ha1 : α₀ < 1) (ht : 0 < t) (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
        (k ! * (k : ℝ) ^ ((2 - α) * k))) := by
  have := coeffA_le_of_spatial (G := waveGreen 1)
    (γ := covEps (volume.withDensity (riesz c α)) ε) (b := 2 - α) ha1 ht (Ksp_nonneg hc hα1) hk
    (fun m hm D hD h hh hsum =>
      (D1Spatial.spatial_riesz_le hc hα0 hα1 (by omega) hD hε hh).2 hk t hsum)
  rwa [show 2 - α + (2 - α₀) = 4 - α - α₀ by ring] at this

/-- **`E:d1-coefficient`, white case, at every width** (`α = 1`, `b = 1`,
`K_sp = c_δ`, `β = 3 - α₀`): `A_k^ε(t) ≤ (2Zc)^k t^{βk}/(k! k^k)`. -/
theorem coeffA_white_le {c α₀ t ε : ℝ} (hc : 0 ≤ c) (ha1 : α₀ < 1) (ht : 0 < t) (hε : 0 < ε)
    {k : ℕ} (hk : 1 ≤ k) :
    coeffA (waveGreen 1) (covEps (whiteCov c) ε) α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) /
        (k ! * (k : ℝ) ^ ((1 : ℝ) * k))) := by
  have := coeffA_le_of_spatial (G := waveGreen 1) (γ := covEps (whiteCov c) ε) (b := 1)
    ha1 ht hc hk (fun m hm D hD h hh hsum => by
      have h1 := (D1Spatial.spatial_white_le hc (by omega) hD hε hh).2 hk t hsum
      rw [one_mul, Real.rpow_natCast, Real.rpow_natCast]
      exact h1)
  rwa [show (1 : ℝ) + (2 - α₀) = 3 - α₀ by ring] at this

/-- Both inequalities of `E:d1-coefficient`, Riesz case, at every width:
the factorial form `(2ZK_sp)^k t^{βk}/(k!)^q`, `q = 3 - α`. -/
theorem coeffA_riesz_le_factorial {c α α₀ t ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (ha1 : α₀ < 1) (ht : 0 < t) (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
        (k ! : ℝ) ^ (3 - α)) := by
  refine (coeffA_riesz_le hc hα0 hα1 ha1 ht hε hk).trans (ENNReal.ofReal_le_ofReal ?_)
  have := div_le_div_factorial (Q := (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k))
    (b := 2 - α) (mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (Zc_pos ha1).le)
      (Ksp_nonneg hc hα1)) _) (Real.rpow_nonneg ht.le _)) (by linarith) k
  rwa [show 2 - α + 1 = 3 - α by ring] at this

/-- Both inequalities of `E:d1-coefficient`, white case, at every width:
`(2Zc)^k t^{βk}/(k!)^2`. -/
theorem coeffA_white_le_factorial {c α₀ t ε : ℝ} (hc : 0 ≤ c) (ha1 : α₀ < 1) (ht : 0 < t)
    (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    coeffA (waveGreen 1) (covEps (whiteCov c) ε) α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! : ℝ) ^ (2 : ℝ)) := by
  refine (coeffA_white_le hc ha1 ht hε hk).trans (ENNReal.ofReal_le_ofReal ?_)
  have := div_le_div_factorial (Q := (2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k)) (b := 1)
    (mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (Zc_pos ha1).le) hc) _)
      (Real.rpow_nonneg ht.le _)) zero_le_one k
  rwa [show (1 : ℝ) + 1 = 2 by norm_num] at this

/-! ### The limit `A_k(t)` -/

/-- **Supplied input `DiagramLimits`** (part of `L:joint-fixed-order`, main TeX
lines 1853-1966, invoked by the proof of `P:d1-upper` at line 5534; the first
clause of `DiagramModel.MixedMoment`): every diagram of the covariance `Γ` in
dimension `d` converges, as the noise width `ε ↓ 0`, to its limit `diagramLim`
(the TeX's `J_{m,n,D}(t)`).  TRUE under `H:homog` by `L:joint-fixed-order`;
assumed, not proved. -/
def DiagramLimits (d : ℕ) (Γ : Measure (Rd d)) (α₀ t : ℝ) : Prop :=
  ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
    Tendsto (fun ε => diagram (waveGreen d) (covEps Γ ε) α₀ m n D t) (𝓝[>] 0)
      (𝓝 (diagramLim d Γ α₀ m n D t))

/-- `MixedMoment` contains `DiagramLimits`. -/
theorem diagramLimits_of_mixedMoment {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (h : MixedMoment d α₀ Γ P X u t) : DiagramLimits d Γ α₀ t :=
  fun m n D hD => (h.1 m n D hD).1

/-- A bound uniform in the width passes to the limit `A_k(t)` (main TeX lines
5534-5537: "The bound is uniform in `ε, δ`, so it passes to `A_k(t)`"). -/
theorem coeffALim_le_of_forall {d : ℕ} {Γ : Measure (Rd d)} {α₀ t : ℝ} {k : ℕ} {R : ℝ≥0∞}
    (hlim : DiagramLimits d Γ α₀ t)
    (hR : ∀ ε : ℝ, 0 < ε → coeffA (waveGreen d) (covEps Γ ε) α₀ k t ≤ R) :
    coeffALim d Γ α₀ k t ≤ R := by
  have hT : Tendsto (fun ε => coeffA (waveGreen d) (covEps Γ ε) α₀ k t) (𝓝[>] 0)
      (𝓝 (coeffALim d Γ α₀ k t)) := by
    unfold coeffA coeffALim
    exact tendsto_finsetSum _ fun m _ => tendsto_finsetSum _ fun D hD => hlim m _ D hD
  exact le_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε => hR ε hε)

/-- **`E:d1-coefficient` for the limit `A_k(t)`, Riesz case**, under
`DiagramLimits`: both inequalities. -/
theorem coeffALim_riesz_le {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (ha1 : α₀ < 1) (ht : 0 < t) (hlim : DiagramLimits 1 (volume.withDensity (riesz c α)) α₀ t)
    {k : ℕ} (hk : 1 ≤ k) :
    coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α)) :=
  ⟨coeffALim_le_of_forall hlim fun _ hε => coeffA_riesz_le hc hα0 hα1 ha1 ht hε hk,
    coeffALim_le_of_forall hlim fun _ hε => coeffA_riesz_le_factorial hc hα0 hα1 ha1 ht hε hk⟩

/-- **`E:d1-coefficient` for the limit `A_k(t)`, white case**, under
`DiagramLimits`: both inequalities. -/
theorem coeffALim_white_le {c α₀ t : ℝ} (hc : 0 ≤ c) (ha1 : α₀ < 1) (ht : 0 < t)
    (hlim : DiagramLimits 1 (whiteCov c) α₀ t) {k : ℕ} (hk : 1 ≤ k) :
    coeffALim 1 (whiteCov c) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) /
          (k ! * (k : ℝ) ^ ((1 : ℝ) * k))) ∧
      coeffALim 1 (whiteCov c) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! : ℝ) ^ (2 : ℝ)) :=
  ⟨coeffALim_le_of_forall hlim fun _ hε => coeffA_white_le hc ha1 ht hε hk,
    coeffALim_le_of_forall hlim fun _ hε => coeffA_white_le_factorial hc ha1 ht hε hk⟩

/-! ### The moment display `E:d1-upper` -/

/-- Auxiliary: `a^k t^{βk} = (a t^β)^k`. -/
theorem pow_mul_rpow_eq {a t β : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    a ^ k * t ^ (β * k) = (a * t ^ β) ^ k := by
  rw [mul_pow, Real.rpow_mul ht, Real.rpow_natCast]

/-- The series step (main TeX lines 5540-5549): under `MixedMoment`, if
`A_k(t) ≤ x^k/(k!)^ν` for every `k ≥ 1` with `ν ≥ 1`, `x ≥ 0`, then
`E u² ≤ exp(ν x^{1/ν})` (the term `A_0 = 1` added separately). -/
theorem secondMoment_le_of_coeff {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (h : MixedMoment d α₀ Γ P X u t) {x ν : ℝ} (hx : 0 ≤ x) (hν : 1 ≤ ν)
    (hco : ∀ k : ℕ, 1 ≤ k → coeffALim d Γ α₀ k t ≤ ENNReal.ofReal (x ^ k / (k ! : ℝ) ^ ν)) :
    ∫ ω, u ω ^ 2 ∂P ≤ Real.exp (ν * x ^ (1 / ν)) := by
  obtain ⟨hs, hle⟩ := SeriesType.seriesNu_summable_le hν hx
  rw [h.secondMoment_eq]
  refine le_trans ?_ hle
  refine Summable.tsum_le_tsum (fun k => ?_) h.2.2.2.summable hs
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [coeffALim_zero]
  · exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hco k hk)

/-- **`E:d1-upper`, Riesz case** (main TeX lines 5464-5467): under the supplied
input `MixedMoment` for `Γ = c|y|^{-α} dy`,
`E u² ≤ exp(C_dir t^κ)` with `C_dir = q(2ZK_sp)^{1/q}`, `κ = β/q`, `q = 3 - α`,
`β = 4 - α - α₀`. -/
theorem secondMoment_riesz_le {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (ha1 : α₀ < 1) (ht : 0 < t) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {u : Ω → ℝ} (h : MixedMoment 1 α₀ (volume.withDensity (riesz c α)) P X u t) :
    ∫ ω, u ω ^ 2 ∂P ≤ Real.exp ((3 - α) * (2 * Zc α₀ * Ksp c α) ^ (1 / (3 - α)) *
      t ^ ((4 - α - α₀) / (3 - α))) := by
  have ha : 0 ≤ 2 * Zc α₀ * Ksp c α :=
    mul_nonneg (mul_nonneg zero_le_two (Zc_pos ha1).le) (Ksp_nonneg hc hα1)
  have hle := secondMoment_le_of_coeff h (x := 2 * Zc α₀ * Ksp c α * t ^ (4 - α - α₀))
    (ν := 3 - α) (mul_nonneg ha (Real.rpow_nonneg ht.le _)) (by linarith) fun k hk => by
      rw [← pow_mul_rpow_eq ht.le]
      exact (coeffALim_riesz_le hc hα0 hα1 ha1 ht (diagramLimits_of_mixedMoment h) hk).2
  rw [Real.mul_rpow ha (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le, mul_one_div,
    ← mul_assoc] at hle
  exact hle

/-- **`E:d1-upper`, white case** (`q = 2`, `β = 3 - α₀`, `K_sp = c_δ`): under
`MixedMoment` for `Γ = c δ₀`, `E u² ≤ exp(2(2Zc)^{1/2} t^{(3-α₀)/2})`. -/
theorem secondMoment_white_le {c α₀ t : ℝ} (hc : 0 ≤ c) (ha1 : α₀ < 1) (ht : 0 < t)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ}
    (h : MixedMoment 1 α₀ (whiteCov c) P X u t) :
    ∫ ω, u ω ^ 2 ∂P ≤ Real.exp (2 * (2 * Zc α₀ * c) ^ (1 / (2 : ℝ)) *
      t ^ ((3 - α₀) / 2)) := by
  have ha : 0 ≤ 2 * Zc α₀ * c := mul_nonneg (mul_nonneg zero_le_two (Zc_pos ha1).le) hc
  have hle := secondMoment_le_of_coeff h (x := 2 * Zc α₀ * c * t ^ (3 - α₀))
    (ν := 2) (mul_nonneg ha (Real.rpow_nonneg ht.le _)) (by norm_num) fun k hk => by
      rw [← pow_mul_rpow_eq ht.le]
      exact (coeffALim_white_le hc ha1 ht (diagramLimits_of_mixedMoment h) hk).2
  rw [Real.mul_rpow ha (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le, mul_one_div,
    ← mul_assoc] at hle
  exact hle

/-! ### Wrappers with the manuscript's hypotheses -/

/-- **`P:d1-upper`, Riesz case of `E:d1-covariances`** (main TeX lines
5454-5468), with the manuscript's hypotheses `0 < α₀ < 1` (line 5315),
`γ = c_α|y|^{-α}`, `0 < α < 1`, `c_α > 0`, `t > 0`, and the supplied input
`MixedMoment` (`P:mixed`, about the unconstructed `u`, `X_n`).  Conclusions:
1. on the model, at every noise width `ε > 0` and every `k ≥ 1`, both
   inequalities of `E:d1-coefficient` for the smoothed `A_k(t)` (no input);
2. `E:d1-coefficient` in the TeX's form
   `A_k(t) = Σ_{m=0}^{2k} E[X_m X_{2k-m}] ≤ (2ZK)^k t^{βk}/(k! k^{bk}) ≤
   (2ZK)^k t^{βk}/(k!)^q`;
3. `E:d1-upper`: `E u² ≤ exp(C_dir t^κ)`, `C_dir = q(2ZK_sp)^{1/q}`, `κ = β/q`.
Carried but unused: `0 < α₀` (only `α₀ < 1` is used); `c_α > 0` is used only
as `c_α ≥ 0`. -/
theorem d1_upper_paper_riesz {c α α₀ t : ℝ} (_hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ}
    (h : MixedMoment 1 α₀ (volume.withDensity (riesz c α)) P X u t) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k →
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α))) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ m ∈ Finset.range (2 * k + 1), ∫ ω, X m ω * X (2 * k - m) ω ∂P ≤
        (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k)) ∧
      (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! * (k : ℝ) ^ ((2 - α) * k)) ≤
        (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, u ω ^ 2 ∂P ≤ Real.exp ((3 - α) * (2 * Zc α₀ * Ksp c α) ^ (1 / (3 - α)) *
      t ^ ((4 - α - α₀) / (3 - α))) := by
  have hQ : ∀ k : ℕ, 0 ≤ (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) := fun k =>
    mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (Zc_pos hα₀1).le)
      (Ksp_nonneg hc.le hα1)) _) (Real.rpow_nonneg ht.le _)
  refine ⟨fun ε hε k hk => ⟨coeffA_riesz_le hc.le hα0 hα1 hα₀1 ht hε hk,
      coeffA_riesz_le_factorial hc.le hα0 hα1 hα₀1 ht hε hk⟩, fun k hk => ⟨?_, ?_⟩,
    secondMoment_riesz_le hc.le hα0 hα1 hα₀1 ht h⟩
  · rw [← h.coeffA_eq k]
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (hQ k) (by positivity))
      (coeffALim_riesz_le hc.le hα0 hα1 hα₀1 ht (diagramLimits_of_mixedMoment h) hk).1
  · have := div_le_div_factorial (hQ k) (b := 2 - α) (by linarith) k
    rwa [show 2 - α + 1 = 3 - α by ring] at this

/-- **`P:d1-upper`, white case of `E:d1-covariances`** (`α = 1`, `γ = c_δ δ₀`,
main TeX lines 5454-5468; `b = 1`, `q = 2`, `β = 3 - α₀`, `K_sp = c_δ`), with the
manuscript's hypotheses `0 < α₀ < 1`, `c_δ > 0`, `t > 0` and the supplied input
`MixedMoment`.  Conclusions as in `d1_upper_paper_riesz`.  Carried but unused:
`0 < α₀`; `c_δ > 0` is used only as `c_δ ≥ 0`. -/
theorem d1_upper_paper_white {c α₀ t : ℝ} (_hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (ht : 0 < t) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {u : Ω → ℝ} (h : MixedMoment 1 α₀ (whiteCov c) P X u t) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k →
      coeffA (waveGreen 1) (covEps (whiteCov c) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) /
          (k ! * (k : ℝ) ^ ((1 : ℝ) * k))) ∧
      coeffA (waveGreen 1) (covEps (whiteCov c) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! : ℝ) ^ (2 : ℝ))) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ m ∈ Finset.range (2 * k + 1), ∫ ω, X m ω * X (2 * k - m) ω ∂P ≤
        (2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! * (k : ℝ) ^ ((1 : ℝ) * k)) ∧
      (2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! * (k : ℝ) ^ ((1 : ℝ) * k)) ≤
        (2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! : ℝ) ^ (2 : ℝ)) ∧
    ∫ ω, u ω ^ 2 ∂P ≤ Real.exp (2 * (2 * Zc α₀ * c) ^ (1 / (2 : ℝ)) *
      t ^ ((3 - α₀) / 2)) := by
  have hQ : ∀ k : ℕ, 0 ≤ (2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) := fun k =>
    mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two (Zc_pos hα₀1).le) hc.le) _)
      (Real.rpow_nonneg ht.le _)
  refine ⟨fun ε hε k hk => ⟨coeffA_white_le hc.le hα₀1 ht hε hk,
      coeffA_white_le_factorial hc.le hα₀1 ht hε hk⟩, fun k hk => ⟨?_, ?_⟩,
    secondMoment_white_le hc.le hα₀1 ht h⟩
  · rw [← h.coeffA_eq k]
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (hQ k) (by positivity))
      (coeffALim_white_le hc.le hα₀1 ht (diagramLimits_of_mixedMoment h) hk).1
  · have := div_le_div_factorial (hQ k) (b := 1) zero_le_one k
    rwa [show (1 : ℝ) + 1 = 2 by norm_num] at this

/-! ### The white case without `DiagramLimits` (L13 integration) -/

/-- Auxiliary: `p_ε * (a Γ) = a (p_ε * Γ)`. -/
theorem covEps_smul {d : ℕ} (a : ℝ≥0∞) (Γ : Measure (Rd d)) (ε : ℝ) (x : Rd d) :
    covEps (a • Γ) ε x = a * covEps Γ ε x := by
  rw [covEps, covEps, lintegral_smul_measure, smul_eq_mul]

/-- Auxiliary: multiplying the covariance density by `a` multiplies every
diagram by `a^{#pairs}` (one covariance factor per pair). -/
theorem diagram_const_mul {d : ℕ} (G : ℝ → Measure (Rd d)) (γ : Rd d → ℝ≥0∞) {a : ℝ≥0∞}
    (ha : a ≠ ⊤) (α₀ : ℝ) (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) (t : ℝ) :
    diagram G (fun x => a * γ x) α₀ m n D t =
      a ^ (openers D).card * diagram G γ α₀ m n D t := by
  have hk : a ^ (openers D).card ≠ ⊤ := ENNReal.pow_ne_top ha
  have hs : ∀ h, spatial G (fun x => a * γ x) m D h =
      a ^ (openers D).card * spatial G γ m D h := by
    intro h
    unfold spatial covWeight
    simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
    exact lintegral_const_mul' _ _ hk
  unfold diagram
  simp_rw [hs, mul_left_comm _ (a ^ (openers D).card)]
  exact lintegral_const_mul' _ _ hk

/-- **`DiagramLimits` holds for white noise in `d = 1`** (`Γ = c δ₀`, `α₀ < 1`):
every diagram converges as `ε ↓ 0` (`WhiteCollapse.tendsto_diagram_white` for
`δ₀`, scaled by `diagram_const_mul`).  This discharges the supplied input of
`coeffALim_white_le` (the TeX's `L:joint-fixed-order`, invoked at main TeX line
5534, in this case). -/
theorem diagramLimits_white (c : ℝ) {α₀ : ℝ} (hα1 : α₀ < 1) (t : ℝ) :
    DiagramLimits 1 (whiteCov c) α₀ t := by
  intro m n D hD
  have he : ∀ ε, covEps (whiteCov c) ε =
      fun x => ENNReal.ofReal c * covEps (Measure.dirac (0 : Rd 1)) ε x :=
    fun ε => funext fun x => covEps_smul _ _ ε x
  have hT : Tendsto (fun ε => diagram (waveGreen 1) (covEps (whiteCov c) ε) α₀ m n D t)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal c ^ (openers D).card *
        WhiteCollapse.whiteDiagram α₀ m n D t)) := by
    simp_rw [he, diagram_const_mul _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.Tendsto.const_mul
      (WhiteCollapse.tendsto_diagram_white hα1 m n (mem_Pi2.1 hD) t)
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  exact tendsto_nhds_limUnder ⟨_, hT⟩

/-- **`E:d1-coefficient` for the limit `A_k(t)`, white case, with no supplied
input**: `coeffALim_white_le` with `DiagramLimits` discharged by
`diagramLimits_white`. -/
theorem coeffALim_white_le' {c α₀ t : ℝ} (hc : 0 ≤ c) (ha1 : α₀ < 1) (ht : 0 < t) {k : ℕ}
    (hk : 1 ≤ k) :
    coeffALim 1 (whiteCov c) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) /
          (k ! * (k : ℝ) ^ ((1 : ℝ) * k))) ∧
      coeffALim 1 (whiteCov c) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! : ℝ) ^ (2 : ℝ)) :=
  coeffALim_white_le hc ha1 ht (diagramLimits_white c ha1 t) hk

/-- **`P:d1-upper`, white case, the coefficient displays with no supplied input**
(main TeX lines 5454-5468 and 5517-5535, `γ = c_δ δ₀`): with the manuscript's
hypotheses `0 < α₀ < 1`, `c_δ > 0`, `t > 0`, both inequalities of
`E:d1-coefficient` hold at every width `ε > 0` and for the limit `A_k(t)`.  The
moment display `E:d1-upper` is not included (it is about `u`; see
`d1_upper_paper_white`, which needs `MixedMoment`).  Carried but unused:
`0 < α₀`; `c_δ > 0` is used only as `c_δ ≥ 0`. -/
theorem d1_upper_paper_white' {c α₀ t : ℝ} (_hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (ht : 0 < t) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k →
      coeffA (waveGreen 1) (covEps (whiteCov c) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) /
          (k ! * (k : ℝ) ^ ((1 : ℝ) * k))) ∧
      coeffA (waveGreen 1) (covEps (whiteCov c) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! : ℝ) ^ (2 : ℝ))) ∧
    (∀ k : ℕ, 1 ≤ k →
      coeffALim 1 (whiteCov c) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) /
          (k ! * (k : ℝ) ^ ((1 : ℝ) * k))) ∧
      coeffALim 1 (whiteCov c) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * c) ^ k * t ^ ((3 - α₀) * k) / (k ! : ℝ) ^ (2 : ℝ))) :=
  ⟨fun _ hε _ hk => ⟨coeffA_white_le hc.le hα₀1 ht hε hk,
      coeffA_white_le_factorial hc.le hα₀1 ht hε hk⟩,
    fun _ hk => coeffALim_white_le' hc.le hα₀1 ht hk⟩

end StratonovichHAMSecondMoment.D1Upper
