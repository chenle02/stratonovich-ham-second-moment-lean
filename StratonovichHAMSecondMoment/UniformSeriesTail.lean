module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:uniform-series-tail` (Uniform series tails from scaled moments) of
`notes/notes_stratonovich_ham_second_moment.tex`, statement lines 3703-3727 and
proof lines 3729-3748 at manuscript revision a284420.

How the proof obtains `‖Y_n‖₂ ≤ B_r^{1/2} r^{-n}` (TeX lines 3730-3733): neither
orthogonality, nor coefficient extraction in `r`, nor scaling of the field.  It
expands `E|u(r)|² = Σ_{m,n} r^{m+n} E[Y_m Y_n]`; all mixed moments
`E[Y_m Y_n]` are nonnegative (`L:terminal-wick`, TeX lines 3600-3645, for a
field with nonnegative covariance), and `r > 0`, so the double sum dominates its
diagonal term `r^{2n} E|Y_n|²`.

Supplied input (the only one), from `L:terminal-wick`: the structure
`TerminalWickInput`, i.e. for the given `r`, absolute `L²` convergence of
`Σ r^n Y_n` and nonnegativity of every mixed moment `E[Y_m Y_n]`.  These are
exactly the two facts the TeX proof cites from `L:terminal-wick` (lines 3730-3731:
"absolute `L²` convergence of every regularized series and nonnegative mixed
moments").  `L:terminal-wick` gives the absolute convergence for every real `r`;
only the given `r` is assumed here.  Nothing about the Gaussian field, the
chain measures or the Wick formula is used beyond these two facts.

Formalized in full:
* `norm_sq_le_of_inner_nonneg`: in a real inner product space, a convergent
  series with pairwise nonnegative inner products dominates each term in norm.
* `term_bound`, `tail_bound`, `uniform_series_tail`,
  `uniform_series_tail_second_moment`: the general Hilbert-space statement, with
  the regularization pairs replaced by an arbitrary index type and an arbitrary
  nontrivial filter, and the hypotheses required only eventually.
* `uniform_series_tail_paper`, `uniform_series_tail_second_moment_paper`: the
  manuscript statement in `L²(Ω, μ)` = `Lp ℝ 2 μ`, regularization pairs
  `(ε, δ) ∈ (0,∞)²`, limit `ε, δ ↓ 0` read as the joint limit along
  `𝓝[>] 0 ×ˢ 𝓝[>] 0`.

Conventions: `E|f|²` is written `∫ ω, (f ω)^2 ∂μ` for `f ∈ L²`; this is a
genuine integral (equal to `‖f‖²`, see `integral_sq_eq_norm_sq`), not a junk
value.  `r^{-n}` is written `(r ^ n)⁻¹`, `B_r^{1/2}` is `Real.sqrt B`; `B ≥ 0`
follows from the moment bound, so no junk value of `Real.sqrt` is reached.
The tail `Σ_{n>N} Z_n` is written `∑' n, Z (n + (N + 1))`.

Differences from the TeX: the terms are real-valued (`Lp ℝ 2 μ`) and `r` is
real, as in the lemma; the fixed point `(T,x)` is implicit in the family `Y`.
The limit `u^{ε,δ}(1) → u` is proved by dominated convergence for series with
the majorant `B^{1/2} r^{-n}` instead of the explicit head/tail split of TeX
lines 3738-3745 (same majorant).  No conclusion is narrower than the TeX.
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace StratonovichHAMSecondMoment.UniformSeriesTail

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The step "the scaled second moment contains the nonnegative term
`r^{2n} E|Y_n|²`" (TeX lines 3731-3733), abstractly: if `Σ v_m` converges to `S`
and all inner products `⟪v_m, v_n⟫` are nonnegative, then `‖v_n‖² ≤ ‖S‖²`. -/
theorem norm_sq_le_of_inner_nonneg (v : ℕ → E) (S : E) (hS : HasSum v S)
    (hpos : ∀ m n, 0 ≤ inner ℝ (v m) (v n)) (n : ℕ) :
    ‖v n‖ ^ 2 ≤ ‖S‖ ^ 2 := by
  -- `⟪v m, S⟫ = Σ_k ⟪v m, v k⟫ ≥ 0`
  have hcol : ∀ m, HasSum (fun k => inner ℝ (v m) (v k)) (inner ℝ (v m) S) := by
    intro m
    simpa using hS.mapL (innerSL ℝ (v m))
  have hcol_nonneg : ∀ m, 0 ≤ inner ℝ (v m) S := fun m =>
    by simpa using hasSum_le (fun k => hpos m k) hasSum_zero (hcol m)
  have hrow : HasSum (fun m => inner ℝ (v m) S) (inner ℝ S S) := by
    have h := hS.mapL (innerSL ℝ S)
    simp only [innerSL_apply_apply] at h
    simpa [real_inner_comm] using h
  have h1 : inner ℝ (v n) (v n) ≤ inner ℝ (v n) S :=
    le_hasSum (hcol n) n (fun k _ => hpos n k)
  have h2 : inner ℝ (v n) S ≤ inner ℝ S S :=
    le_hasSum hrow n (fun m _ => hcol_nonneg m)
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact h1.trans h2

variable [CompleteSpace E]

/-- The term bound `‖Y_n‖ ≤ B^{1/2} r^{-n}` of `(E:uniform-series-tail)` for one
sequence (TeX lines 3730-3733), from absolute convergence of `Σ r^n Y_n`,
nonnegative mixed inner products and `‖Σ r^n Y_n‖² ≤ B`, for `r > 0`. -/
theorem term_bound (Y : ℕ → E) (r B : ℝ) (hr : 0 < r)
    (hsum : Summable fun n => ‖r ^ n • Y n‖)
    (hpos : ∀ m n, 0 ≤ inner ℝ (Y m) (Y n))
    (hB : ‖∑' n, r ^ n • Y n‖ ^ 2 ≤ B) (n : ℕ) :
    ‖Y n‖ ≤ Real.sqrt B * (r ^ n)⁻¹ := by
  have hS : HasSum (fun n => r ^ n • Y n) (∑' n, r ^ n • Y n) :=
    (Summable.of_norm hsum).hasSum
  have hpos' : ∀ m k, 0 ≤ inner ℝ (r ^ m • Y m) (r ^ k • Y k) := by
    intro m k
    rw [real_inner_smul_left, real_inner_smul_right]
    exact mul_nonneg (pow_nonneg hr.le _) (mul_nonneg (pow_nonneg hr.le _) (hpos m k))
  have h := (norm_sq_le_of_inner_nonneg _ _ hS hpos' n).trans hB
  have hrn : 0 < r ^ n := pow_pos hr n
  rw [norm_smul, Real.norm_of_nonneg hrn.le] at h
  have h' : r ^ n * ‖Y n‖ ≤ Real.sqrt B := by
    apply Real.le_sqrt_of_sq_le
    simpa [mul_pow] using h
  rw [le_mul_inv_iff₀ hrn, mul_comm]
  exact h'

/-- Auxiliary geometric identity: `Σ_n c r^{-(n+N+1)} = c r^{-(N+1)}/(1 - r^{-1})`
for `r > 1` (route helper for `tail_bound`). -/
theorem hasSum_geometric_tail (c r : ℝ) (hr : 1 < r) (N : ℕ) :
    HasSum (fun n : ℕ => c * (r ^ (n + (N + 1)))⁻¹)
      (c * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hq0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hq1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (c * (r ^ (N + 1))⁻¹)
  convert h using 1
  · funext n
    rw [pow_add, mul_inv, inv_pow]
    ring
  · rw [div_eq_mul_inv]

/-- Auxiliary: `Σ_n c r^{-n}` converges for `r > 1` (route helper). -/
theorem summable_geometric_mul {c r : ℝ} (hr : 1 < r) :
    Summable fun n : ℕ => c * (r ^ n)⁻¹ := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have h := (summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le)
    (inv_lt_one_of_one_lt₀ hr)).mul_left c
  simpa [inv_pow] using h

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The tail bounds of `(E:uniform-series-tail)` and absolute convergence from a
geometric term bound (TeX lines 3734-3736, "the geometric series and the
triangle inequality"): if `‖Z_n‖ ≤ c r^{-n}` with `r > 1`, then `Σ ‖Z_n‖ < ∞`
and `‖Σ_{n>N} Z_n‖ ≤ c r^{-(N+1)}/(1 - r^{-1})`. -/
theorem tail_bound (Z : ℕ → E) (c r : ℝ) (hr : 1 < r)
    (hZ : ∀ n, ‖Z n‖ ≤ c * (r ^ n)⁻¹) :
    (Summable fun n => ‖Z n‖) ∧
      ∀ N : ℕ, ‖∑' n, Z (n + (N + 1))‖ ≤ c * (r ^ (N + 1))⁻¹ / (1 - r⁻¹) := by
  have hsum0 : Summable fun n : ℕ => c * (r ^ n)⁻¹ :=
    summable_geometric_mul (c := c) hr
  refine ⟨Summable.of_nonneg_of_le (fun n => norm_nonneg _) hZ hsum0, fun N => ?_⟩
  exact tsum_of_norm_bounded (hasSum_geometric_tail c r hr N) (fun n => hZ _)

/-- The general form of `L:uniform-series-tail` (TeX lines 3703-3748) in a real
Hilbert space `E`, for an arbitrary index type `ι` of regularizations and a
nontrivial filter `F` on it (the manuscript: `(ε,δ) ∈ (0,∞)²`, `ε,δ ↓ 0`).
Hypotheses, required eventually along `F`: absolute convergence of
`Σ r^n Y^i_n`, nonnegative inner products `⟪Y^i_m, Y^i_n⟫` (the
`L:terminal-wick` input) and `‖Σ r^n Y^i_n‖² ≤ B`; and `Y^i_n → X_n` for each
`n`.  Conclusions: eventually along `F`, the term bound, absolute convergence of
`Σ Y^i_n` and its tail bounds; the same three for `X`; and
`Σ Y^i_n → Σ X_n` along `F`.  Route difference: the final limit is taken by
Mathlib's dominated convergence for series (`tendsto_tsum_of_dominated_convergence`)
with the summable majorant `B^{1/2} r^{-n}`, instead of the TeX's explicit
head/tail split at level `N` (lines 3738-3745); the majorant is the one the TeX
split uses. -/
theorem uniform_series_tail {ι : Type*} (F : Filter ι) [F.NeBot]
    (Y : ι → ℕ → E) (X : ℕ → E) (r B : ℝ) (hr : 1 < r)
    (hsum : ∀ᶠ i in F, Summable fun n => ‖r ^ n • Y i n‖)
    (hpos : ∀ᶠ i in F, ∀ m n, 0 ≤ inner ℝ (Y i m) (Y i n))
    (hB : ∀ᶠ i in F, ‖∑' n, r ^ n • Y i n‖ ^ 2 ≤ B)
    (hX : ∀ n, Tendsto (fun i => Y i n) F (𝓝 (X n))) :
    (∀ᶠ i in F, (∀ n, ‖Y i n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
        (Summable fun n => ‖Y i n‖) ∧
        ∀ N : ℕ, ‖∑' n, Y i (n + (N + 1))‖ ≤
          Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ n, ‖X n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (Summable fun n => ‖X n‖) ∧
      (∀ N : ℕ, ‖∑' n, X (n + (N + 1))‖ ≤
        Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      Tendsto (fun i => ∑' n, Y i n) F (𝓝 (∑' n, X n)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hYb : ∀ᶠ i in F, ∀ n, ‖Y i n‖ ≤ Real.sqrt B * (r ^ n)⁻¹ := by
    filter_upwards [hsum, hpos, hB] with i h1 h2 h3
    exact term_bound (Y i) r B hr0 h1 h2 h3
  have hXb : ∀ n, ‖X n‖ ≤ Real.sqrt B * (r ^ n)⁻¹ := fun n =>
    le_of_tendsto (hX n).norm (hYb.mono fun i hi => hi n)
  have hXt := tail_bound X _ r hr hXb
  refine ⟨?_, hXb, hXt.1, hXt.2, ?_⟩
  · filter_upwards [hYb] with i hi
    exact ⟨hi, tail_bound (Y i) _ r hr hi⟩
  · exact tendsto_tsum_of_dominated_convergence (summable_geometric_mul hr) hX hYb

/-- The last sentence of `L:uniform-series-tail` (TeX lines 3725-3726 and
3746) in the general setting of `uniform_series_tail`: if moreover
`‖Σ Y^i_n‖² ≤ B₁` eventually along `F`, then `‖Σ X_n‖² ≤ B₁` ("continuity of the
`L²` norm"). -/
theorem uniform_series_tail_second_moment {ι : Type*} (F : Filter ι) [F.NeBot]
    (Y : ι → ℕ → E) (X : ℕ → E) (r B B₁ : ℝ) (hr : 1 < r)
    (hsum : ∀ᶠ i in F, Summable fun n => ‖r ^ n • Y i n‖)
    (hpos : ∀ᶠ i in F, ∀ m n, 0 ≤ inner ℝ (Y i m) (Y i n))
    (hB : ∀ᶠ i in F, ‖∑' n, r ^ n • Y i n‖ ^ 2 ≤ B)
    (hX : ∀ n, Tendsto (fun i => Y i n) F (𝓝 (X n)))
    (hB₁ : ∀ᶠ i in F, ‖∑' n, Y i n‖ ^ 2 ≤ B₁) :
    ‖∑' n, X n‖ ^ 2 ≤ B₁ :=
  le_of_tendsto
    (((uniform_series_tail F Y X r B hr hsum hpos hB hX).2.2.2.2).norm.pow 2) hB₁

end Hilbert

section L2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Auxiliary: `E[f g] = ⟪f, g⟫` in `L²(Ω, μ)`. -/
theorem integral_mul_eq_inner (f g : Lp ℝ 2 μ) :
    ∫ ω, f ω * g ω ∂μ = inner ℝ f g := by
  rw [L2.inner_def]
  congr 1
  ext ω
  simp [mul_comm]

/-- Auxiliary: `E|f|² = ‖f‖²` in `L²(Ω, μ)` (so the integral below is never a
junk value). -/
theorem integral_sq_eq_norm_sq (f : Lp ℝ 2 μ) :
    ∫ ω, (f ω) ^ 2 ∂μ = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext ω
  simp [sq]

/-- Supplied input from `L:terminal-wick` (TeX lines 3600-3645 at a284420; the two facts at 3638-3644), for
one regularized family of terms `Y_n ∈ L²(Ω)` and the given real `r`: absolute
`L²` convergence of `Σ r^n Y_n` (the lemma's last sentence, which gives it for
every real or complex `r`) and nonnegativity of every mixed moment
`E[Y_m Y_n]` (the lemma's Wick formula with nonnegative pairing integrals when
the covariance is nonnegative; zero when `m + n` is odd).  These are exactly the
two facts the proof of `L:uniform-series-tail` cites (TeX lines 3730-3731). -/
structure TerminalWickInput (μ : Measure Ω) (Y : ℕ → Lp ℝ 2 μ) (r : ℝ) : Prop where
  abs_summable : Summable fun n => ‖r ^ n • Y n‖
  mixed_moment_nonneg : ∀ m n, 0 ≤ ∫ ω, Y m ω * Y n ω ∂μ

/-- Auxiliary: positive regularization pairs eventually along `ε, δ ↓ 0`. -/
theorem eventually_pos_pair :
    ∀ᶠ p : ℝ × ℝ in (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)), 0 < p.1 ∧ 0 < p.2 := by
  have h := prod_mem_prod (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  filter_upwards [h] with p hp
  exact ⟨hp.1, hp.2⟩

/-- `L:uniform-series-tail` (TeX lines 3703-3727, proof 3729-3748 at a284420),
exact-hypothesis wrapper in `L²(Ω, μ)` for a probability measure `μ`.
Regularized terms `Y ε δ n` for `ε, δ > 0`; `u^{ε,δ}(r) = Σ r^n Y^{ε,δ}_n`.
Hypotheses: `r > 1`; for every `ε, δ > 0` the `L:terminal-wick` input
`TerminalWickInput` (absolute convergence at `r`, nonnegative mixed moments) and
`E|u^{ε,δ}(r)|² ≤ B` (the uniform bound `sup_{ε,δ>0} E|u^{ε,δ}(r)|² ≤ B_r`);
`Y^{ε,δ}_n → X_n` in `L²` as `ε, δ ↓ 0` jointly, for each `n`.
Conclusions: `Σ X_n` converges absolutely in `L²`; `u^{ε,δ}(1) → u = Σ X_n` in
`L²`; `‖Y^{ε,δ}_n‖₂, ‖X_n‖₂ ≤ B^{1/2} r^{-n}`; the tail bounds
`‖Σ_{n>N} Y^{ε,δ}_n‖₂, ‖Σ_{n>N} X_n‖₂ ≤ B^{1/2} r^{-(N+1)}/(1 - r^{-1})`; and,
as part of the estimates, absolute convergence of each `Σ Y^{ε,δ}_n`.
`IsProbabilityMeasure μ` is the manuscript's setting and is not used by the
proof. -/
theorem uniform_series_tail_paper [IsProbabilityMeasure μ]
    (Y : ℝ → ℝ → ℕ → Lp ℝ 2 μ) (X : ℕ → Lp ℝ 2 μ) (r B : ℝ) (hr : 1 < r)
    (hTW : ∀ ε δ : ℝ, 0 < ε → 0 < δ → TerminalWickInput μ (Y ε δ) r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • Y ε δ n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B)
    (hX : ∀ n, Tendsto (fun p : ℝ × ℝ => Y p.1 p.2 n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n))) :
    (Summable fun n => ‖X n‖) ∧
      Tendsto (fun p : ℝ × ℝ => ∑' n, Y p.1 p.2 n)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (∑' n, X n)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n, ‖Y ε δ n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ n, ‖X n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ N : ℕ,
        ‖∑' n, Y ε δ (n + (N + 1))‖ ≤ Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ N : ℕ, ‖∑' n, X (n + (N + 1))‖ ≤
        Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → Summable fun n => ‖Y ε δ n‖) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hpos' : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ m n, 0 ≤ inner ℝ (Y ε δ m) (Y ε δ n) :=
    fun ε δ hε hδ m n => by
      rw [← integral_mul_eq_inner]; exact (hTW ε δ hε hδ).mixed_moment_nonneg m n
  have hB' : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ‖∑' n, r ^ n • Y ε δ n‖ ^ 2 ≤ B :=
    fun ε δ hε hδ => by rw [← integral_sq_eq_norm_sq]; exact hB ε δ hε hδ
  have hYb : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n, ‖Y ε δ n‖ ≤ Real.sqrt B * (r ^ n)⁻¹ :=
    fun ε δ hε hδ => term_bound (Y ε δ) r B hr0 (hTW ε δ hε hδ).abs_summable
      (hpos' ε δ hε hδ) (hB' ε δ hε hδ)
  have hgen := uniform_series_tail (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
    (fun p n => Y p.1 p.2 n) X r B hr
    (eventually_pos_pair.mono fun p hp => (hTW p.1 p.2 hp.1 hp.2).abs_summable)
    (eventually_pos_pair.mono fun p hp => hpos' p.1 p.2 hp.1 hp.2)
    (eventually_pos_pair.mono fun p hp => hB' p.1 p.2 hp.1 hp.2) hX
  obtain ⟨-, hXb, hXs, hXt, hlim⟩ := hgen
  exact ⟨hXs, hlim, hYb, hXb,
    fun ε δ hε hδ => (tail_bound (Y ε δ) _ r hr (hYb ε δ hε hδ)).2, hXt,
    fun ε δ hε hδ => (tail_bound (Y ε δ) _ r hr (hYb ε δ hε hδ)).1⟩

/-- The last sentence of `L:uniform-series-tail` (TeX lines 3725-3726; proof
line 3746 at a284420), exact-hypothesis wrapper: under the hypotheses of
`uniform_series_tail_paper`, if also `E|u^{ε,δ}(1)|² ≤ B₁` for all `ε, δ > 0`,
then `E|u|² ≤ B₁` for `u = Σ X_n`.  `IsProbabilityMeasure μ` is not used. -/
theorem uniform_series_tail_second_moment_paper [IsProbabilityMeasure μ]
    (Y : ℝ → ℝ → ℕ → Lp ℝ 2 μ) (X : ℕ → Lp ℝ 2 μ) (r B B₁ : ℝ) (hr : 1 < r)
    (hTW : ∀ ε δ : ℝ, 0 < ε → 0 < δ → TerminalWickInput μ (Y ε δ) r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • Y ε δ n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B)
    (hX : ∀ n, Tendsto (fun p : ℝ × ℝ => Y p.1 p.2 n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n)))
    (hB₁ : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, Y ε δ n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B₁) :
    ∫ ω, ((∑' n, X n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B₁ := by
  have hlim := (uniform_series_tail_paper Y X r B hr hTW hB hX).2.1
  rw [integral_sq_eq_norm_sq]
  refine le_of_tendsto (hlim.norm.pow 2) ?_
  filter_upwards [eventually_pos_pair] with p hp
  rw [← integral_sq_eq_norm_sq]
  exact hB₁ p.1 p.2 hp.1 hp.2

end L2

end StratonovichHAMSecondMoment.UniformSeriesTail
