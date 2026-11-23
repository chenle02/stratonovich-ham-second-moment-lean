/-! ## Bridges (untrusted helpers)

The copies in `ChallengeDefs` that the elaborator does not identify with the project's
definitions by unfolding: the inductive `Trig` and the structure `HomogCovariance`
(new inductive types, so only equivalent, not equal) and the structurally recursive
`counts`, `raw`, `cut` (equal pointwise, proved by induction). Everything here is
proved; nothing is assumed. -/

namespace StratonovichHamSecondMomentLeanAuditBridge

namespace HermiteWord

variable {C B V : Type} [DecidableEq C]

theorem counts_eq (w : List (C × B)) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.counts w =
      StratonovichHAMAudit.HermiteWord.counts w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.bump a.1
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.counts w) =
      StratonovichHAMAudit.HermiteWord.bump a.1 (StratonovichHAMAudit.HermiteWord.counts w)
    rw [ih]; rfl

theorem raw_eq (J : C → V → V) (F : B → V → V) (v₀ : V) (w : List (C × B)) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.raw J F v₀ w =
      StratonovichHAMAudit.HermiteWord.raw J F v₀ w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show F a.2 (J a.1 (StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.raw
        J F v₀ w)) = F a.2 (J a.1 (StratonovichHAMAudit.HermiteWord.raw J F v₀ w))
    rw [ih]

theorem cut_eq (P : V → V) (J : C → V → V) (F : B → V → V) (v₀ : V) (w : List (C × B)) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.cut P J F v₀ w =
      StratonovichHAMAudit.HermiteWord.cut P J F v₀ w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show F a.2 (P (J a.1 (P (StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.cut
        P J F v₀ w)))) = F a.2 (P (J a.1 (P (StratonovichHAMAudit.HermiteWord.cut P J F v₀ w))))
    rw [ih]

end HermiteWord

namespace MaskedTrigProducts

/-- The copied `Trig` to the project's, constructor by constructor. -/
def toP : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig →
    StratonovichHAMSecondMoment.MaskedTrigProducts.Trig
  | .cos => .cos
  | .sin => .sin

theorem eval_eq (k : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (x : ℝ) : k.eval x = (toP k).eval x := by
  cases k <;> rfl

theorem coef1_eq (k : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (σ : Bool) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 k σ =
      StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 (toP k) σ := by
  cases k <;> cases σ <;> rfl

theorem coef_eq (P Q : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (j : Bool × Bool) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.coef P Q j =
      StratonovichHAMSecondMoment.MaskedTrigProducts.coef (toP P) (toP Q) j := by
  show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 P j.1 *
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 Q j.2 =
    StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 (toP P) j.1 *
      StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 (toP Q) j.2
  rw [coef1_eq, coef1_eq]

theorem prodFn_eq (I : Set ℝ) (A : ℝ → ℂ)
    (P Q : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (r ρ : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn I A P Q r ρ =
      StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn I A (toP P) (toP Q) r ρ := by
  show I.indicator (fun t => A t * P.eval (r * t) * Q.eval (ρ * t)) =
    I.indicator (fun t => A t * (toP P).eval (r * t) * (toP Q).eval (ρ * t))
  simp only [eval_eq]

end MaskedTrigProducts

namespace HomogHypothesis

/-- The copied `HomogCovariance` gives the project's, field by field (each field's type
unfolds to the same proposition). -/
theorem homog_toP {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance
      d alpha alpha0 Γ μ) :
    StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ :=
  ⟨h.dim, h.alpha0_pos, h.alpha0_lt_one, h.Γ_radon, h.Γ_even, h.Γ_tempered, h.Γ_posdef,
    h.μ_radon, h.μ_even, h.μ_tempered, h.spectral, h.scaling, h.threshold, h.alpha_range⟩

end HomogHypothesis


/-! ### Structures copied in `ChallengeDefs`: field-by-field conversions both ways

Each copy has the project's fields with the same (unfolding-equal) types, so the anonymous
constructor over the numeric projections converts in either direction. -/

namespace IndexedCone

universe u

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

def gToP (G : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.GroundFamily F) : StratonovichHAMSecondMoment.IndexedCone.GroundFamily F :=
  ⟨G.1, G.2, G.3, G.4, G.5, G.6, G.7, G.8, G.9, G.10, G.11, G.12, G.13, G.14, G.15, G.16, G.17⟩

def gOfP (G : StratonovichHAMSecondMoment.IndexedCone.GroundFamily F) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.GroundFamily F :=
  ⟨G.1, G.2, G.3, G.4, G.5, G.6, G.7, G.8, G.9, G.10, G.11, G.12, G.13, G.14, G.15, G.16, G.17⟩

def cToP {G : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.GroundFamily F} {ϱ : ℝ}
    (C : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.ConeConstants G ϱ) : StratonovichHAMSecondMoment.IndexedCone.ConeConstants (gToP G) ϱ :=
  ⟨C.1, C.2, C.3, C.4, C.5, C.6, C.7, C.8, C.9, C.10, C.11, C.12, C.13, C.14, C.15, C.16, C.17, C.18, C.19, C.20, C.21, C.22, C.23, C.24, C.25, C.26, C.27, C.28, C.29, C.30, C.31, C.32, C.33, C.34, C.35, C.36, C.37, C.38, C.39, C.40, C.41, C.42, C.43, C.44, C.45, C.46⟩

def cOfP {G : StratonovichHAMSecondMoment.IndexedCone.GroundFamily F} {ϱ : ℝ}
    (C : StratonovichHAMSecondMoment.IndexedCone.ConeConstants G ϱ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.ConeConstants (gOfP G) ϱ :=
  ⟨C.1, C.2, C.3, C.4, C.5, C.6, C.7, C.8, C.9, C.10, C.11, C.12, C.13, C.14, C.15, C.16, C.17, C.18, C.19, C.20, C.21, C.22, C.23, C.24, C.25, C.26, C.27, C.28, C.29, C.30, C.31, C.32, C.33, C.34, C.35, C.36, C.37, C.38, C.39, C.40, C.41, C.42, C.43, C.44, C.45, C.46⟩

end IndexedCone

namespace WeakSobolev

variable {d : ℕ}

theorem rtToP {V : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ} {f : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ}
    {g : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.HomogHypothesis.Rd d}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g) : StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

theorem rtOfP {V : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ} {f : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ}
    {g : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.HomogHypothesis.Rd d}
    (h : StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem rt_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial = @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial := by
  funext d V f g
  exact propext ⟨rtToP, rtOfP⟩

end WeakSobolev

namespace HomogHypothesis

theorem homog_ofP {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem homog_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance = @StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance := by
  funext d alpha alpha0 Γ μ
  exact propext ⟨homog_toP, homog_ofP⟩

end HomogHypothesis



/-! ### Definitions whose copies unfold to a copied predicate: equal as functions -/

namespace WeakSobolev

theorem rayleighSet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighSet = @StratonovichHAMSecondMoment.WeakSobolev.rayleighSet := by
  funext d V
  show {q | ∃ f g, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g ∧
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighValue V f g = q} =
    {q | ∃ f g, StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g ∧ StratonovichHAMSecondMoment.WeakSobolev.rayleighValue V f g = q}
  rw [rt_eq]
  rfl

theorem rayleighRate_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighRate = @StratonovichHAMSecondMoment.WeakSobolev.rayleighRate := by
  funext d V
  show Real.sqrt (sSup (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighSet V)) =
    Real.sqrt (sSup (StratonovichHAMSecondMoment.WeakSobolev.rayleighSet V))
  rw [rayleighSet_eq]

end WeakSobolev

namespace VariationalDilation

theorem rate_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.rate = @StratonovichHAMSecondMoment.VariationalDilation.rate := by
  funext d a Γ Ψ s
  show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighRate (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean a Γ Ψ s) =
    StratonovichHAMSecondMoment.WeakSobolev.rayleighRate (StratonovichHAMSecondMoment.VariationalDilation.mean a Γ Ψ s)
  rw [WeakSobolev.rayleighRate_eq]
  rfl

theorem integratedRate_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.integratedRate = @StratonovichHAMSecondMoment.VariationalDilation.integratedRate := by
  funext d a Γ Ψ
  show ∫ s in Set.Ioo (0 : ℝ) 1, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.rate a Γ Ψ s =
    ∫ s in Set.Ioo (0 : ℝ) 1, StratonovichHAMSecondMoment.VariationalDilation.rate a Γ Ψ s
  rw [rate_eq]

end VariationalDilation

namespace IndexedCone

theorem chainState_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.chainState = @StratonovichHAMSecondMoment.IndexedCone.chainState := by
  funext F _ _ D B e0 m
  induction m with
  | zero => rfl
  | succ m ih =>
    show D m B (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.chainState D B e0 m) = D m B (StratonovichHAMSecondMoment.IndexedCone.chainState D B e0 m)
    rw [ih]

theorem scalarFamily_eq : gToP StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.scalarFamily = StratonovichHAMSecondMoment.IndexedCone.scalarFamily := rfl

end IndexedCone

namespace TimeCompletion

/-- The copied `TimeParams` to the project's, field by field. -/
def tpToP (p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.TimeParams) : StratonovichHAMSecondMoment.TimeCompletion.TimeParams :=
  ⟨p.1, p.2, p.3, p.4, p.5⟩

def tpOfP (p : StratonovichHAMSecondMoment.TimeCompletion.TimeParams) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.TimeParams :=
  ⟨p.1, p.2, p.3, p.4, p.5⟩

end TimeCompletion

namespace DampedNormsHomog

theorem gmToP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass G) : StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass G :=
  ⟨h.1⟩

theorem gmOfP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass G) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass G :=
  ⟨h.1⟩

end DampedNormsHomog

namespace MaskedContinuousWave

/-- The copied `Wave` to the project's, constructor by constructor. -/
def toP : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave → StratonovichHAMSecondMoment.MaskedContinuousWave.Wave
  | .c => .c
  | .b => .b

theorem weval_eq (W : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r t : ℝ) :
    W.eval r t = (toP W).eval r t := by
  cases W <;> rfl

theorem amp_eq (W : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.amp W r = StratonovichHAMSecondMoment.MaskedContinuousWave.amp (toP W) r := by
  cases W <;> rfl

theorem fr_eq (W : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.fr W r = StratonovichHAMSecondMoment.MaskedContinuousWave.fr (toP W) r := by
  cases W <;> rfl

theorem trig_eq (W : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r : ℝ) :
    MaskedTrigProducts.toP (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.trig W r) =
      StratonovichHAMSecondMoment.MaskedContinuousWave.trig (toP W) r := by
  cases W
  · rfl
  · show MaskedTrigProducts.toP (if r < 1 then .cos else .sin) = (if r < 1 then .cos else .sin)
    split_ifs <;> rfl

theorem waveFn_eq (I : Set ℝ) (F G : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r ρ : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn I F G r ρ =
      StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn I (toP F) (toP G) r ρ := by
  cases F <;> cases G <;> rfl

end MaskedContinuousWave

/-! ### Wave L6: the structure `TypeContinuityInputs`, and definitions whose copies unfold
to a copied structure, predicate or inductive (equal as functions) -/

namespace TypeContinuity

theorem tciToP {d : ℕ} {alpha : ℝ} {mom : ℕ → ℝ → ℝ → ℝ} {c : ℕ → ℝ → ℕ → ℝ} {L0 : ℝ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs d alpha mom c L0) :
    StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs d alpha mom c L0 :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩

theorem tciOfP {d : ℕ} {alpha : ℝ} {mom : ℕ → ℝ → ℝ → ℝ} {c : ℕ → ℝ → ℕ → ℝ} {L0 : ℝ}
    (h : StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs d alpha mom c L0) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs d alpha mom c L0 :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem tci_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs =
    @StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs := by
  funext d alpha mom c L0
  exact propext ⟨tciToP, tciOfP⟩

end TypeContinuity

namespace VariationalRate

theorem scoreSet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.scoreSet =
    @StratonovichHAMSecondMoment.VariationalRate.scoreSet := by
  funext d a Γ c
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.scoreSet
    StratonovichHAMSecondMoment.VariationalRate.scoreSet
  rw [VariationalDilation.integratedRate_eq]
  rfl

theorem score1Set_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.score1Set =
    @StratonovichHAMSecondMoment.VariationalRate.score1Set := by
  funext d a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.score1Set
    StratonovichHAMSecondMoment.VariationalRate.score1Set
  rw [VariationalDilation.integratedRate_eq]
  rfl

theorem testRadius_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.testRadius =
    @StratonovichHAMSecondMoment.VariationalRate.testRadius := by
  funext d alpha a Γ Ψ₀
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.testRadius
    StratonovichHAMSecondMoment.VariationalRate.testRadius
  rw [VariationalDilation.integratedRate_eq]
  rfl

theorem S1Bdd_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.S1Bdd =
    @StratonovichHAMSecondMoment.VariationalRate.S1Bdd := by
  funext d a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.S1Bdd
    StratonovichHAMSecondMoment.VariationalRate.S1Bdd
  rw [score1Set_eq]

theorem S1pos_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.S1pos =
    @StratonovichHAMSecondMoment.VariationalRate.S1pos := by
  funext d a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.S1pos
    StratonovichHAMSecondMoment.VariationalRate.S1pos
  rw [score1Set_eq]

end VariationalRate

namespace SpatialStaticControls

theorem lamSq_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lamSq =
    @StratonovichHAMSecondMoment.SpatialStaticControls.lamSq := by
  funext d U c
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lamSq
    StratonovichHAMSecondMoment.SpatialStaticControls.lamSq
  rw [WeakSobolev.rayleighSet_eq]

theorem lam_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lam =
    @StratonovichHAMSecondMoment.SpatialStaticControls.lam := by
  funext d U c
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lam
    StratonovichHAMSecondMoment.SpatialStaticControls.lam
  rw [WeakSobolev.rayleighRate_eq]

theorem lamZ_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lamZ =
    @StratonovichHAMSecondMoment.SpatialStaticControls.lamZ := by
  funext d Γ z c
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lamZ
    StratonovichHAMSecondMoment.SpatialStaticControls.lamZ
  rw [lam_eq]
  rfl

theorem rayleighFloor_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor =
      @StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor := by
  funext d Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor
    StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor
  rw [WeakSobolev.rayleighSet_eq]
  rfl

end SpatialStaticControls

namespace SpatialSmoothRatio

theorem staticControls_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialSmoothRatio.StaticControls =
      @StratonovichHAMSecondMoment.SpatialSmoothRatio.StaticControls := by
  funext d a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialSmoothRatio.StaticControls
    StratonovichHAMSecondMoment.SpatialSmoothRatio.StaticControls
  rw [WeakSobolev.rayleighSet_eq, WeakSobolev.rayleighRate_eq, VariationalDilation.integratedRate_eq]
  rfl

end SpatialSmoothRatio

namespace WaveTwoVariances

/-- The kernel entries agree: for each of the four index pairs the copied `rowWave`,
`colWave` reduce to the copied constructors, whose `eval` unfolds to the project's. -/
theorem kernelEntry_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kernelEntry =
    @StratonovichHAMSecondMoment.WaveTwoVariances.kernelEntry := by
  funext d i j ξ η t
  fin_cases i <;> fin_cases j <;> rfl

theorem maskedKernel_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel =
    @StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel := by
  funext d s h i j ξ η
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel
    StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel
  rw [kernelEntry_eq]

theorem kernelLp_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp =
    @StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp := by
  funext d T s h i j ξ η
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp
    StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp
  exact MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [maskedKernel_eq])

theorem rowWave_toP (i : Fin 2) :
    MaskedContinuousWave.toP (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.rowWave i) =
      StratonovichHAMSecondMoment.WaveTwoVariances.rowWave i := by
  fin_cases i <;> rfl

theorem colWave_toP (j : Fin 2) :
    MaskedContinuousWave.toP (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.colWave j) =
      StratonovichHAMSecondMoment.WaveTwoVariances.colWave j := by
  fin_cases j <;> rfl

/-- The copied `emb` over a copied `TimeParams` is the project's over the converted
parameters, on equal functions. -/
theorem emb_eq (p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.TimeParams)
    (f g : ℝ → ℂ) (hf : f ∈ StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.L2fun p.T)
    (hg : g ∈ StratonovichHAMSecondMoment.TimeCompletion.L2fun (TimeCompletion.tpToP p).T) (e : f = g) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.emb p ⟨f, hf⟩ =
      StratonovichHAMSecondMoment.TimeCompletion.emb (TimeCompletion.tpToP p) ⟨g, hg⟩ := by
  subst e
  rfl

/-- `kerH` over a copied `TimeParams` is the project's over the converted parameters. -/
theorem kerH_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kerH =
    fun p => @StratonovichHAMSecondMoment.WaveTwoVariances.kerH (TimeCompletion.tpToP p) := by
  funext p d s h i j ξ η
  show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.extL2 p
      (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp p.T s h i j ξ η) =
    StratonovichHAMSecondMoment.TimeCompletion.extL2 (TimeCompletion.tpToP p)
      (StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp p.T s h i j ξ η)
  rw [kernelLp_eq]
  rfl

theorem coef_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.coef =
    fun p => @StratonovichHAMSecondMoment.WaveTwoVariances.coef (TimeCompletion.tpToP p) := by
  funext p d s h U V l
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.coef
  rw [kerH_eq]
  rfl

theorem inputBound_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.InputBound =
    fun p => @StratonovichHAMSecondMoment.WaveTwoVariances.InputBound (TimeCompletion.tpToP p) := by
  funext p d s h ν γ M
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.InputBound
  rw [kerH_eq, coef_eq]
  rfl

theorem outputBound_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.OutputBound =
    fun p => @StratonovichHAMSecondMoment.WaveTwoVariances.OutputBound (TimeCompletion.tpToP p) := by
  funext p d s h ν γ M
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.OutputBound
  rw [kerH_eq, coef_eq]
  rfl

end WaveTwoVariances

namespace UniformSeriesTail

/-! The copied structure `TerminalWickInput` (wave L7) is a new `Prop`-valued structure:
equivalent to the project's, hence equal by `propext`. -/

theorem twiToP {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {Y : ℕ → MeasureTheory.Lp ℝ 2 μ} {r : ℝ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput μ Y r) :
    StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput μ Y r :=
  ⟨h.1, h.2⟩

theorem twiOfP {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {Y : ℕ → MeasureTheory.Lp ℝ 2 μ} {r : ℝ}
    (h : StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput μ Y r) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput μ Y r :=
  ⟨h.1, h.2⟩

theorem twi_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput =
    @StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput := by
  funext Ω _ μ Y r
  exact propext ⟨twiToP, twiOfP⟩

end UniformSeriesTail

namespace OccupationPhysicalClass

/-! The copied structures `SquarePairingBounds` and `IsOccField` (wave L7) are new
`Prop`-valued structures: equivalent to the project's, hence equal by `propext`; the copied
`energySet` and `EstarO`, which mention `IsOccField`, are then equal to the project's. -/

theorem spbToP {d : ℕ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {alpha R : ℝ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds Γ alpha R) :
    StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds Γ alpha R :=
  ⟨h.1, h.2⟩

theorem spbOfP {d : ℕ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {alpha R : ℝ}
    (h : StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds Γ alpha R) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds Γ alpha R :=
  ⟨h.1, h.2⟩

theorem spb_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds =
    @StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds := by
  funext d Γ alpha R
  exact propext ⟨spbToP, spbOfP⟩

theorem occToP {d : ℕ} {G : ℝ → StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ}
    {DG : ℝ → StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.HomogHypothesis.Rd d}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField G DG) :
    StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField G DG :=
  ⟨h.1, h.2, h.3, h.4⟩

theorem occOfP {d : ℕ} {G : ℝ → StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ}
    {DG : ℝ → StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.HomogHypothesis.Rd d}
    (h : StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField G DG) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField G DG :=
  ⟨h.1, h.2, h.3, h.4⟩

theorem occ_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField =
    @StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField := by
  funext d G DG
  exact propext ⟨occToP, occOfP⟩

theorem energySet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.energySet =
    @StratonovichHAMSecondMoment.OccupationPhysicalClass.energySet := by
  funext d a D Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.energySet StratonovichHAMSecondMoment.OccupationPhysicalClass.energySet
  rw [occ_eq]
  rfl

theorem EstarO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.EstarO =
    @StratonovichHAMSecondMoment.OccupationPhysicalClass.EstarO := by
  funext d a D Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.EstarO StratonovichHAMSecondMoment.OccupationPhysicalClass.EstarO
  rw [energySet_eq]

end OccupationPhysicalClass

namespace DampedMultiplier

/-! The copied structure `GreenFourier` (wave L8) is a new `Prop`-valued structure:
equivalent to the project's, hence equal by `propext`. -/

theorem gfToP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier G) : StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier G :=
  ⟨h.1, h.2⟩

theorem gfOfP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier G) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier G :=
  ⟨h.1, h.2⟩

theorem gf_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier = @StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier := by
  funext d G
  exact propext ⟨gfToP, gfOfP⟩

end DampedMultiplier

namespace SpaceTimePositivity

/-! The copied structure `SpaceTimeCS` of `SpaceTimePositivity` (wave L8): a new
`Prop`-valued structure, equal to the project's by `propext`. -/

theorem stcsToP {d : ℕ} {a : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS a Γ) : StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS a Γ :=
  ⟨h.1, h.2, h.3⟩

theorem stcsOfP {d : ℕ} {a : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS a Γ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS a Γ :=
  ⟨h.1, h.2, h.3⟩

theorem stcs_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS = @StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS := by
  funext d a Γ
  exact propext ⟨stcsToP, stcsOfP⟩

end SpaceTimePositivity

namespace OccupationCeilingFinite

/-! The copied structure `SpaceTimeCS` of `OccupationCeilingFinite` (wave L8): a new
`Prop`-valued structure, equal to the project's by `propext`. -/

theorem stcsToP {d : ℕ} {a : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS a Γ) : StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS a Γ :=
  ⟨h.1, h.2, h.3⟩

theorem stcsOfP {d : ℕ} {a : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS a Γ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS a Γ :=
  ⟨h.1, h.2, h.3⟩

theorem stcs_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS = @StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS := by
  funext d a Γ
  exact propext ⟨stcsToP, stcsOfP⟩

end OccupationCeilingFinite

namespace FiniteWick

/-! The copied structure `CenteredGaussianField` (wave L8): a new `Prop`-valued
structure, equal to the project's by `propext`. -/

theorem cgfToP {X Ω : Type*} [MeasurableSpace Ω] {W : X → Ω → ℝ} {K : X → X → ℝ}
    {P : MeasureTheory.Measure Ω} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P) :
    StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P :=
  ⟨h.1, h.2⟩

theorem cgfOfP {X Ω : Type*} [MeasurableSpace Ω] {W : X → Ω → ℝ} {K : X → X → ℝ}
    {P : MeasureTheory.Measure Ω} (h : StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P :=
  ⟨h.1, h.2⟩

theorem cgf_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField =
    @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField := by
  funext X Ω _ W K P
  exact propext ⟨cgfToP, cgfOfP⟩

end FiniteWick

namespace SymplecticFree

/-! The copied structure `FreeWaveData` (wave L8) carries data (the group `S`, the
reversal `R`, the translations `τ`), so it is not equal to the project's; the converters
rebuild one from the other field by field, and the fields of the result reduce to those
of the argument. -/

/-- A copied `FreeWaveData` as the project's (same fields). -/
def fwdToP {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree.FreeWaveData d E) : StratonovichHAMSecondMoment.SymplecticFree.FreeWaveData d E :=
  ⟨F.1, F.2, F.3, F.4, F.5, F.6, F.7, F.8, F.9, F.10⟩

/-- A project `FreeWaveData` as the copy (same fields). -/
def fwdOfP {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : StratonovichHAMSecondMoment.SymplecticFree.FreeWaveData d E) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree.FreeWaveData d E :=
  ⟨F.1, F.2, F.3, F.4, F.5, F.6, F.7, F.8, F.9, F.10⟩

/-- The structurally recursive `orderedProd` (wave L8): equal to the project's, by
induction on the index. -/
theorem orderedProd_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree.orderedProd = @StratonovichHAMSecondMoment.SymplecticFree.orderedProd := by
  funext E _ _ Q n
  induction n with
  | zero => rfl
  | succ n ih =>
    show Q (n + 1) * StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree.orderedProd Q n = Q (n + 1) * StratonovichHAMSecondMoment.SymplecticFree.orderedProd Q n
    rw [ih]

end SymplecticFree

namespace TerminalWick

/-! The structurally recursive `chainWeight` and `chainWeightReal` (wave L8): equal to the
project's, by induction on the number of points; the copied `chainMass` and
`chainMassReal`, their integrals, are then equal to the project's. -/

theorem chainWeight_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainWeight = @StratonovichHAMSecondMoment.TerminalWick.chainWeight := by
  funext d n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext T s
    show (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then
          StratonovichHAMSecondMoment.WaveGreen.waveGreen d (T - s (Fin.last n)) Set.univ else 0) *
        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainWeight d n (s (Fin.last n)) (Fin.init s) =
      (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then
          StratonovichHAMSecondMoment.WaveGreen.waveGreen d (T - s (Fin.last n)) Set.univ else 0) *
        StratonovichHAMSecondMoment.TerminalWick.chainWeight d n (s (Fin.last n)) (Fin.init s)
    rw [ih]

theorem chainWeightReal_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainWeightReal = @StratonovichHAMSecondMoment.TerminalWick.chainWeightReal := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext T s
    show (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then ENNReal.ofReal (T - s (Fin.last n)) else 0) *
        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainWeightReal n (s (Fin.last n)) (Fin.init s) =
      (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then ENNReal.ofReal (T - s (Fin.last n)) else 0) *
        StratonovichHAMSecondMoment.TerminalWick.chainWeightReal n (s (Fin.last n)) (Fin.init s)
    rw [ih]

theorem chainMass_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainMass = @StratonovichHAMSecondMoment.TerminalWick.chainMass := by
  funext d n T
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainMass StratonovichHAMSecondMoment.TerminalWick.chainMass
  rw [chainWeight_eq]

theorem chainMassReal_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainMassReal = @StratonovichHAMSecondMoment.TerminalWick.chainMassReal := by
  funext n T
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainMassReal StratonovichHAMSecondMoment.TerminalWick.chainMassReal
  rw [chainWeightReal_eq]

end TerminalWick

namespace DampedNormsHomog

/-- `GreenMass` as an equation, for the wave-L8 statements that mention it inside a
conjunction (where the converters above do not reach). -/
theorem gm_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass = @StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass := by
  funext d G
  exact propext ⟨gmToP, gmOfP⟩

end DampedNormsHomog

namespace RemoveMask

/-! The copied `maskedRate` (wave L8) is `rayleighRate` of a masked mean, and the copied
`rayleighRate` is equal to the project's only by `rayleighRate_eq`; so are `maskedRate`,
`maskedIntegratedRate` and the named input `RawBlockOriginalLower` built from them. -/

theorem maskedRate_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.maskedRate = @StratonovichHAMSecondMoment.RemoveMask.maskedRate := by
  funext d a Γ Ψ R t
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.maskedRate StratonovichHAMSecondMoment.RemoveMask.maskedRate
  rw [WeakSobolev.rayleighRate_eq]
  try rfl

theorem maskedIntegratedRate_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.maskedIntegratedRate = @StratonovichHAMSecondMoment.RemoveMask.maskedIntegratedRate := by
  funext d a Γ Ψ R
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.maskedIntegratedRate StratonovichHAMSecondMoment.RemoveMask.maskedIntegratedRate
  rw [maskedRate_eq]

theorem rawBlock_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.RawBlockOriginalLower = @StratonovichHAMSecondMoment.RemoveMask.RawBlockOriginalLower := by
  funext d a Γ Ψ v L
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.RawBlockOriginalLower StratonovichHAMSecondMoment.RemoveMask.RawBlockOriginalLower
  rw [maskedIntegratedRate_eq]

end RemoveMask

namespace SpatialBracket

/-- The copied named input `OccupationCeilingK0` (wave L8) mentions `integratedRate`,
equal to the project's only by `integratedRate_eq`. -/
theorem occK0_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0 = @StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0 := by
  funext d alpha a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0 StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0
  rw [VariationalDilation.integratedRate_eq]
  try rfl

end SpatialBracket

namespace RawOccupationEnergy

/-! The copied sets `ratioSet` and `energySet` of `RawOccupationEnergy` (wave L9) quantify over
the copied structure `IsOccField`: equal to the project's through `occ_eq`, and hence so are
their suprema `Cocc` and `EO`. -/

theorem ratioSet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet = @StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet := by
  funext d a alpha Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet
  rw [OccupationPhysicalClass.occ_eq]
  rfl

theorem Cocc_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc = @StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc := by
  funext d a alpha Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc
  rw [ratioSet_eq]

theorem energySet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.energySet = @StratonovichHAMSecondMoment.RawOccupationEnergy.energySet := by
  funext d a Γ ζ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.energySet StratonovichHAMSecondMoment.RawOccupationEnergy.energySet
  rw [OccupationPhysicalClass.occ_eq]
  rfl

theorem EO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.EO = @StratonovichHAMSecondMoment.RawOccupationEnergy.EO := by
  funext d a Γ ζ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.EO StratonovichHAMSecondMoment.RawOccupationEnergy.EO
  rw [energySet_eq]

end RawOccupationEnergy

namespace PhaseContractions

/-! The copied structure `PhaseCovariance` (wave L9) is a new `Prop`-valued structure:
equivalent to the project's, hence equal by `propext`. -/

theorem pcToP {alpha : ℝ} {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance alpha Γ μ) :
    StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance alpha Γ μ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩

theorem pcOfP {alpha : ℝ} {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)}
    (h : StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance alpha Γ μ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance alpha Γ μ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩

theorem pc_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance = @StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance := by
  funext alpha Γ μ
  exact propext ⟨pcToP, pcOfP⟩

end PhaseContractions

namespace FixedSplit

/-- The structurally recursive partial words: equal to the project's, by induction. -/
theorem wordSeq_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit.wordSeq = @StratonovichHAMSecondMoment.FixedSplit.wordSeq := by
  funext E Pr τ op w n
  induction n with
  | zero => rfl
  | succ j ih =>
    show op (τ (j + 1)) (Pr (τ (j + 1)) (τ j) (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit.wordSeq Pr τ op w j)) =
      op (τ (j + 1)) (Pr (τ (j + 1)) (τ j) (StratonovichHAMSecondMoment.FixedSplit.wordSeq Pr τ op w j))
    rw [ih]

/-- The chronological word, through `wordSeq_eq`. -/
theorem word_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit.word = @StratonovichHAMSecondMoment.FixedSplit.word := by
  funext ι E A C a b T J Pr w z t
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit.word StratonovichHAMSecondMoment.FixedSplit.word
  (rw [wordSeq_eq]) <;> rfl

/-- The Fock-model inputs of the fixed split, through `word_eq`. -/
theorem SplitInputs_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit.SplitInputs = @StratonovichHAMSecondMoment.FixedSplit.SplitInputs := by
  funext
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit.SplitInputs StratonovichHAMSecondMoment.FixedSplit.SplitInputs
  (rw [word_eq]) <;> rfl

end FixedSplit

namespace FiniteWordCutoff

/-! Wave L11: the structurally recursive `counts`, `raw`, `cut` of `FiniteWordCutoff`
(native copies of `HermiteWord`'s): equal to the project's, by induction; `cutWordC` and
`DuhamelWords`, which unfold to them, then equal too. -/

theorem counts_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.counts = @StratonovichHAMSecondMoment.FiniteWordCutoff.counts := by
  funext C B _ w
  induction w with
  | nil => rfl
  | cons a w ih =>
    show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.bump a.1 (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.counts w) =
      StratonovichHAMSecondMoment.FiniteWordCutoff.bump a.1 (StratonovichHAMSecondMoment.FiniteWordCutoff.counts w)
    rw [ih]; rfl

theorem raw_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.raw = @StratonovichHAMSecondMoment.FiniteWordCutoff.raw := by
  funext C B V J F v₀ w
  induction w with
  | nil => rfl
  | cons a w ih =>
    show F a.2 (J a.1 (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.raw J F v₀ w)) =
      F a.2 (J a.1 (StratonovichHAMSecondMoment.FiniteWordCutoff.raw J F v₀ w))
    rw [ih]

theorem cut_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.cut = @StratonovichHAMSecondMoment.FiniteWordCutoff.cut := by
  funext C B V P' J F v₀ w
  induction w with
  | nil => rfl
  | cons a w ih =>
    show F a.2 (P' (J a.1 (P' (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.cut P' J F v₀ w)))) =
      F a.2 (P' (J a.1 (P' (StratonovichHAMSecondMoment.FiniteWordCutoff.cut P' J F v₀ w))))
    rw [ih]

theorem cutWordC_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.cutWordC = @StratonovichHAMSecondMoment.FiniteWordCutoff.cutWordC := by
  funext
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.cutWordC StratonovichHAMSecondMoment.FiniteWordCutoff.cutWordC
  (rw [raw_eq]) <;> rfl

theorem duhamelWords_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.DuhamelWords = @StratonovichHAMSecondMoment.FiniteWordCutoff.DuhamelWords := by
  funext
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff.DuhamelWords StratonovichHAMSecondMoment.FiniteWordCutoff.DuhamelWords
  (rw [counts_eq, raw_eq, cutWordC_eq]) <;> rfl

end FiniteWordCutoff

namespace StaticInteractionCompleted

/-! Wave L11: the copied `Prop`-valued structure `CPInputs`: equivalent, hence equal. -/

theorem cpiToP {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {A0 B : H →L[ℂ] H} {n : ℕ} {alpha h R : ℝ} {Cop Fop Hop Q' : ℂ → H →L[ℂ] H}
    {J : ℂ → ℝ → H →L[ℂ] H}
    (c : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs A0 B n alpha h R Cop Fop Hop Q' J) :
    StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs A0 B n alpha h R Cop Fop Hop Q' J :=
  ⟨c.1, c.2, c.3, c.4, c.5, c.6⟩

theorem cpiOfP {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {A0 B : H →L[ℂ] H} {n : ℕ} {alpha h R : ℝ} {Cop Fop Hop Q' : ℂ → H →L[ℂ] H}
    {J : ℂ → ℝ → H →L[ℂ] H}
    (c : StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs A0 B n alpha h R Cop Fop Hop Q' J) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs A0 B n alpha h R Cop Fop Hop Q' J :=
  ⟨c.1, c.2, c.3, c.4, c.5, c.6⟩

end StaticInteractionCompleted

namespace FockColumnBound

/-! Wave L11: the copied data structure `L2Map` (a new structure type): converters both ways,
field by field. -/

def l2ToP {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (T : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound.L2Map μ) : StratonovichHAMSecondMoment.FockColumnBound.L2Map μ :=
  ⟨T.F, T.C, T.C_ne_top, T.meas, T.bound, T.add, T.smul⟩

def l2OfP {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (T : StratonovichHAMSecondMoment.FockColumnBound.L2Map μ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound.L2Map μ :=
  ⟨T.F, T.C, T.C_ne_top, T.meas, T.bound, T.add, T.smul⟩

end FockColumnBound

namespace TerminalWickInputs

/-! Wave L11: the measures built on the recursive `chainWeightReal`: equal to the project's,
through `TerminalWick.chainWeightReal_eq`. -/

theorem timeMeasure_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs.timeMeasure = @StratonovichHAMSecondMoment.TerminalWickInputs.timeMeasure := by
  funext n T
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs.timeMeasure StratonovichHAMSecondMoment.TerminalWickInputs.timeMeasure
  rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainWeightReal_eq]

theorem chainMeasureRaw_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasureRaw = @StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasureRaw := by
  funext d n T x
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasureRaw StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasureRaw
  rw [timeMeasure_eq]; rfl

theorem chainMeasure_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasure = @StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasure := by
  funext d n T hT x
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasure StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasure
  rw [chainMeasureRaw_eq]; rfl

end TerminalWickInputs

namespace TerminalWickRegularization

theorem noiseMeasure_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickRegularization.noiseMeasure = @StratonovichHAMSecondMoment.TerminalWickRegularization.noiseMeasure := by
  funext d n T
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickRegularization.noiseMeasure StratonovichHAMSecondMoment.TerminalWickRegularization.noiseMeasure
  rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickInputs.timeMeasure_eq]; rfl

theorem chainMeasureReg_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickRegularization.chainMeasureReg = @StratonovichHAMSecondMoment.TerminalWickRegularization.chainMeasureReg := by
  funext d n T hT x η
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickRegularization.chainMeasureReg StratonovichHAMSecondMoment.TerminalWickRegularization.chainMeasureReg
  rw [noiseMeasure_eq]; rfl

end TerminalWickRegularization

namespace StaticInteractionCompleted

/-- The structurally recursive block product: equal to the project's, by induction. -/
theorem blockIter_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.StaticInteractionCompleted.blockIter = @StratonovichHAMSecondMoment.StaticInteractionCompleted.blockIter := by
  funext E _ _ S I k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    show S k (I k (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.StaticInteractionCompleted.blockIter S I k x)) =
      S k (I k (StratonovichHAMSecondMoment.StaticInteractionCompleted.blockIter S I k x))
    rw [ih]

theorem cpi_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs = @StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs := by
  funext H _ _ A0 B n alpha h R Cop Fop Hop Q' J
  exact propext ⟨cpiToP, cpiOfP⟩

end StaticInteractionCompleted

/-! ### Wave L13/L14 copies

The Prop structures `Good`, `IsCov`, `EndpointPair`, `ProductParams`, `IsClassO` (field by
field, then `propext`), the data structures `TParams`, `SpData`, `ThreeMomentModel`, `Cx`
(field by field, both ways) and the inductive `Component` (constructor by constructor). -/

namespace VariationalMeanDerivatives

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {S : Set E} {Φ : E → F}

theorem goodToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good S Φ) :
    StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good S Φ :=
  ⟨h.1, h.2, h.3⟩

theorem goodOfP (h : StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good S Φ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good S Φ :=
  ⟨h.1, h.2, h.3⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem good_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good =
    @StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good := by
  funext E _ _ F _ _ S Φ
  exact propext ⟨goodToP, goodOfP⟩

end VariationalMeanDerivatives

namespace EndpointLemmas

theorem icToP {n : ℕ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd n)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.IsCov Γ) :
    StratonovichHAMSecondMoment.EndpointLemmas.IsCov Γ :=
  ⟨h.1, h.2, h.3, h.4⟩

theorem icOfP {n : ℕ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd n)}
    (h : StratonovichHAMSecondMoment.EndpointLemmas.IsCov Γ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.IsCov Γ :=
  ⟨h.1, h.2, h.3, h.4⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem ic_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.IsCov =
    @StratonovichHAMSecondMoment.EndpointLemmas.IsCov := by
  funext n Γ
  exact propext ⟨icToP, icOfP⟩

theorem epToP {θ χ : ℝ} {Γ L S : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.EndpointPair θ χ Γ L S) :
    StratonovichHAMSecondMoment.EndpointLemmas.EndpointPair θ χ Γ L S :=
  ⟨icToP h.1, icToP h.2, h.3, h.4, h.5⟩

theorem epOfP {θ χ : ℝ} {Γ L S : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)}
    (h : StratonovichHAMSecondMoment.EndpointLemmas.EndpointPair θ χ Γ L S) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.EndpointPair θ χ Γ L S :=
  ⟨icOfP h.1, icOfP h.2, h.3, h.4, h.5⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem ep_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.EndpointPair =
    @StratonovichHAMSecondMoment.EndpointLemmas.EndpointPair := by
  funext θ χ Γ L S
  exact propext ⟨epToP, epOfP⟩

theorem ppToP {a : Fin 3 → ℝ} {θ : ℝ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.ProductParams a θ) :
    StratonovichHAMSecondMoment.EndpointLemmas.ProductParams a θ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩

theorem ppOfP {a : Fin 3 → ℝ} {θ : ℝ}
    (h : StratonovichHAMSecondMoment.EndpointLemmas.ProductParams a θ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.ProductParams a θ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem pp_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas.ProductParams =
    @StratonovichHAMSecondMoment.EndpointLemmas.ProductParams := by
  funext a θ
  exact propext ⟨ppToP, ppOfP⟩

end EndpointLemmas

namespace ClassOBridge

theorem coToP {d : ℕ} {u : ℝ → StratonovichHAMSecondMoment.ClassOH1.H1R d}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.IsClassO u) :
    StratonovichHAMSecondMoment.ClassOBridge.IsClassO u :=
  ⟨h.1, h.2, h.3⟩

theorem coOfP {d : ℕ} {u : ℝ → StratonovichHAMSecondMoment.ClassOH1.H1R d}
    (h : StratonovichHAMSecondMoment.ClassOBridge.IsClassO u) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.IsClassO u :=
  ⟨h.1, h.2, h.3⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem co_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.IsClassO =
    @StratonovichHAMSecondMoment.ClassOBridge.IsClassO := by
  funext d u
  exact propext ⟨coToP, coOfP⟩

end ClassOBridge

namespace OccupationCompletion

/-- The copied `TParams` to the project's, field by field. -/
def tpToP (p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams) :
    StratonovichHAMSecondMoment.OccupationCompletion.TParams :=
  ⟨p.1, p.2, p.3⟩

def tpOfP (p : StratonovichHAMSecondMoment.OccupationCompletion.TParams) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams :=
  ⟨p.1, p.2, p.3⟩

/-- The copied `SpData` to the project's, field by field. -/
def spToP {d : ℕ} (S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d) :
    StratonovichHAMSecondMoment.OccupationCompletion.SpData d :=
  ⟨S.1, S.2, S.3, S.4, S.5⟩

def spOfP {d : ℕ} (S : StratonovichHAMSecondMoment.OccupationCompletion.SpData d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d :=
  ⟨S.1, S.2, S.3, S.4, S.5⟩

end OccupationCompletion

namespace EndpointCorollaries

/-- The copied `ThreeMomentModel` to the project's, field by field. -/
def tmToP (M : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.ThreeMomentModel) :
    StratonovichHAMSecondMoment.EndpointCorollaries.ThreeMomentModel :=
  ⟨M.1, M.2, M.3⟩

def tmOfP (M : StratonovichHAMSecondMoment.EndpointCorollaries.ThreeMomentModel) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.ThreeMomentModel :=
  ⟨M.1, M.2, M.3⟩

/-- The copied `Component` to the project's, constructor by constructor. -/
def compToP : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component →
    StratonovichHAMSecondMoment.EndpointCorollaries.Component
  | .product c a => .product c a
  | .riesz c => .riesz c
  | .plane c a => .plane c a

end EndpointCorollaries

namespace MaskedAuxiliaryReal

universe u

/-- The copied complexification to the project's, field by field. -/
def cxToP {H : Type u} (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) :
    StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H :=
  ⟨x.re, x.im⟩

def cxOfP {H : Type u} (x : StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H :=
  ⟨x.re, x.im⟩

/-- `cxToP` is injective (structure eta). -/
theorem cx_inj {H : Type u} {x y : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H}
    (h : cxToP x = cxToP y) : x = y :=
  congrArg cxOfP h

/-- `Cx.ext` for the copy, from the project's. -/
theorem cx_ext {H : Type u} {x y : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H}
    (h1 : x.re = y.re) (h2 : x.im = y.im) : x = y :=
  cx_inj (StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.ext (x := cxToP x) (y := cxToP y) h1 h2)

/-- `Cx.ext_iff` for the copy, from the project's. -/
theorem cx_ext_iff {H : Type u} {x y : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H} :
    x = y ↔ x.re = y.re ∧ x.im = y.im :=
  ⟨fun h => (StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.ext_iff (x := cxToP x) (y := cxToP y)).1
      (congrArg cxToP h),
    fun h => cx_inj ((StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.ext_iff (x := cxToP x) (y := cxToP y)).2 h)⟩

section Inner

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The copied complexification and the project's, as complex inner product spaces: the
field-by-field map is a complex linear isometric equivalence (each operation unfolds to the
same componentwise formula). -/
def cxE : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H ≃ₗᵢ[ℂ]
    StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H where
  toFun := cxToP
  invFun := cxOfP
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

theorem cxE_apply (x : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) :
    cxE x = cxToP x := rfl

/-- `Cx.instCompleteSpace` for the copy: transported along the isometry `cxE` from the
project's instance. -/
theorem cx_completeSpace [CompleteSpace H] :
    CompleteSpace (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) :=
  (cxE (H := H)).toLinearIsometry.isometry.isUniformInducing.completeSpace_congr
    (cxE (H := H)).surjective |>.2 inferInstance

/-- `Cx.instSeparableSpace` for the copy: the image of the project's separable space under
the continuous surjection `cxE⁻¹`. -/
theorem cx_separableSpace [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) :=
  (cxE (H := H)).symm.surjective.denseRange.separableSpace (cxE (H := H)).symm.continuous

variable {d : ℕ}

theorem cxE_cxS (F : SchwartzMap (StratonovichHAMSecondMoment.HomogHypothesis.Rd d) H)
    (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    cxE (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F x) =
      StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F x := rfl

/-- `cxS_apply` for the copy, from the project's. -/
theorem cxS_apply (F : SchwartzMap (StratonovichHAMSecondMoment.HomogHypothesis.Rd d) H)
    (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F x =
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.ofRealCLM (F x) :=
  cx_inj (StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS_apply F x)

/-- `mask_cxS` for the copy, from the project's. -/
theorem mask_cxS (ζ : SchwartzMap (StratonovichHAMSecondMoment.HomogHypothesis.Rd d) ℝ) (R : ℝ)
    (F : SchwartzMap (StratonovichHAMSecondMoment.HomogHypothesis.Rd d) H) :
    (fun x => (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.zetaR ζ R x : ℂ) •
        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F x) =
      fun x => StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.ofRealCLM
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.zetaR ζ R x • F x) := by
  funext x
  exact cx_inj (congrFun (StratonovichHAMSecondMoment.MaskedAuxiliaryReal.mask_cxS ζ R F) x)

/-- The transform of the copied complexified map, carried by `cxE`, is the project's. -/
theorem cxE_paperHat (F : SchwartzMap (StratonovichHAMSecondMoment.HomogHypothesis.Rd d) H)
    (ξ : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    cxE (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.paperHat
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F :
          StratonovichHAMSecondMoment.HomogHypothesis.Rd d →
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) ξ) =
      StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.paperHat
        (StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F :
          StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) ξ := by
  show cxE ((_ : ℂ) • ∫ x, _) = (_ : ℂ) • ∫ x, _
  rw [LinearIsometryEquiv.map_smul]
  exact congrArg (fun v => (StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.cd d : ℂ) • v)
    ((cxE (H := H)).toContinuousLinearEquiv.integral_comp_comm _).symm

/-- `paperHat_cxS_re` for the copy, from the project's. -/
theorem paperHat_cxS_re [CompleteSpace H] (F : SchwartzMap (StratonovichHAMSecondMoment.HomogHypothesis.Rd d) H)
    (ξ : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.paperHat
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F :
          StratonovichHAMSecondMoment.HomogHypothesis.Rd d →
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) ξ).re =
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.cd d •
        ∫ x, Real.cos (inner ℝ ξ x) • F x := by
  have h := congrArg StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.re (cxE_paperHat F ξ)
  exact h.trans (StratonovichHAMSecondMoment.MaskedAuxiliaryReal.paperHat_cxS_re F ξ)

/-- `paperHat_cxS_im` for the copy, from the project's. -/
theorem paperHat_cxS_im [CompleteSpace H] (F : SchwartzMap (StratonovichHAMSecondMoment.HomogHypothesis.Rd d) H)
    (ξ : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.paperHat
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F :
          StratonovichHAMSecondMoment.HomogHypothesis.Rd d →
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) ξ).im =
      -(StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.cd d •
        ∫ x, Real.sin (inner ℝ ξ x) • F x) := by
  have h := congrArg StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.im (cxE_paperHat F ξ)
  exact h.trans (StratonovichHAMSecondMoment.MaskedAuxiliaryReal.paperHat_cxS_im F ξ)

/-- `norm_sq_paperHat_cx` for the copy, from the project's (`cxE` is isometric). -/
theorem norm_sq_paperHat_cx [CompleteSpace H] (F : SchwartzMap (StratonovichHAMSecondMoment.HomogHypothesis.Rd d) H)
    (ξ : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    ‖StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.paperHat
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.cxS F :
          StratonovichHAMSecondMoment.HomogHypothesis.Rd d →
            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx H) ξ‖ ^ 2 =
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.cd d ^ 2 *
        (‖∫ x, Real.cos (inner ℝ ξ x) • F x‖ ^ 2 + ‖∫ x, Real.sin (inner ℝ ξ x) • F x‖ ^ 2) := by
  rw [← (cxE (H := H)).norm_map, cxE_paperHat]
  exact StratonovichHAMSecondMoment.MaskedAuxiliaryReal.norm_sq_paperHat_cx F ξ

end Inner

end MaskedAuxiliaryReal

namespace ClassOBridge

/-! The value sets over the class `𝒪` and their suprema mention the copied `IsClassO`. -/

theorem energySetO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.energySetO = @StratonovichHAMSecondMoment.ClassOBridge.energySetO := by
  funext d a D Γ
  delta StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.energySetO StratonovichHAMSecondMoment.ClassOBridge.energySetO
  rw [co_eq]
  rfl

theorem ratioSetO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.ratioSetO = @StratonovichHAMSecondMoment.ClassOBridge.ratioSetO := by
  funext d a alpha Γ
  delta StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.ratioSetO StratonovichHAMSecondMoment.ClassOBridge.ratioSetO
  rw [co_eq]
  rfl

theorem rawEnergySetO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.rawEnergySetO = @StratonovichHAMSecondMoment.ClassOBridge.rawEnergySetO := by
  funext d a Γ ζ
  delta StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.rawEnergySetO StratonovichHAMSecondMoment.ClassOBridge.rawEnergySetO
  rw [co_eq]
  rfl

theorem EstarClassO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.EstarClassO = @StratonovichHAMSecondMoment.ClassOBridge.EstarClassO := by
  funext d a D Γ
  delta StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.EstarClassO StratonovichHAMSecondMoment.ClassOBridge.EstarClassO
  rw [energySetO_eq]

theorem CoccO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.CoccO = @StratonovichHAMSecondMoment.ClassOBridge.CoccO := by
  funext d a alpha Γ
  delta StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.CoccO StratonovichHAMSecondMoment.ClassOBridge.CoccO
  rw [ratioSetO_eq]

theorem EOO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.EOO = @StratonovichHAMSecondMoment.ClassOBridge.EOO := by
  funext d a Γ ζ
  delta StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge.EOO StratonovichHAMSecondMoment.ClassOBridge.EOO
  rw [rawEnergySetO_eq]

end ClassOBridge

namespace EndpointCorollaries

/-- The copied named input `ThreeTransfer` (it mentions the copied `IsCov`, `EndpointPair`
and `ThreeMomentModel`) gives the project's for the converted model. -/
theorem ttToP {Mdl : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.ThreeMomentModel} {α₀ θ : ℝ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.ThreeTransfer Mdl α₀ θ) :
    StratonovichHAMSecondMoment.EndpointCorollaries.ThreeTransfer (tmToP Mdl) α₀ θ :=
  fun α Γ L S h1 h2 h3 h4 h5 h6 hC hS hne hE =>
    h α Γ L S h1 h2 h3 h4 h5 h6 (EndpointLemmas.icOfP hC) hS hne (EndpointLemmas.epOfP hE)

theorem ttOfP {Mdl : StratonovichHAMSecondMoment.EndpointCorollaries.ThreeMomentModel} {α₀ θ : ℝ}
    (h : StratonovichHAMSecondMoment.EndpointCorollaries.ThreeTransfer Mdl α₀ θ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.ThreeTransfer (tmOfP Mdl) α₀ θ :=
  fun α Γ L S h1 h2 h3 h4 h5 h6 hC hS hne hE =>
    h α Γ L S h1 h2 h3 h4 h5 h6 (EndpointLemmas.icToP hC) hS hne (EndpointLemmas.epToP hE)

/-- `Component.Valid` of a copied component is the project's of the converted one. -/
theorem valid_toP {α : ℝ} {c : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component.Valid α c) :
    StratonovichHAMSecondMoment.EndpointCorollaries.Component.Valid α (compToP c) := by
  cases c <;> exact h

/-- The component measures of a copied component are the project's of the converted one. -/
theorem meas_eq (α : ℝ) (c : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component.meas α c = StratonovichHAMSecondMoment.EndpointCorollaries.Component.meas α (compToP c) := by
  cases c <;> rfl

theorem low_eq (θ : ℝ) (c : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component.low θ c = StratonovichHAMSecondMoment.EndpointCorollaries.Component.low θ (compToP c) := by
  cases c <;> rfl

theorem st_eq (α θ : ℝ) (c : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component.st α θ c = StratonovichHAMSecondMoment.EndpointCorollaries.Component.st α θ (compToP c) := by
  cases c <;> rfl

end EndpointCorollaries

/-! ### Wave L15 copies

The data structures `CutoffProfile`, `CameronSpatialMap` and `UniformMeanRegulator` (field by
field, both ways; the regulator's `Tsp` converted pointwise) and the Prop structure `UM0Facts`
(field by field). -/

namespace UniformMeanInterface

/-- The copied `CutoffProfile` to the project's, field by field. -/
def cpToP {d : ℕ} (c : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d) :
    StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d :=
  ⟨c.1, c.2, c.3, c.4, c.5, c.6, c.7⟩

def cpOfP {d : ℕ} (c : StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d :=
  ⟨c.1, c.2, c.3, c.4, c.5, c.6, c.7⟩

/-- The copied `CameronSpatialMap` to the project's, field by field. -/
def csmToP {d : ℕ} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
    {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {R : ℝ}
    (T : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CameronSpatialMap S η R) :
    StratonovichHAMSecondMoment.UniformMeanInterface.CameronSpatialMap (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spToP S) (cpToP η) R :=
  ⟨T.1, T.2, T.3, T.4, T.5⟩

def csmOfP {d : ℕ} {S : StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
    {η : StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {R : ℝ}
    (T : StratonovichHAMSecondMoment.UniformMeanInterface.CameronSpatialMap S η R) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CameronSpatialMap (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spOfP S) (cpOfP η) R :=
  ⟨T.1, T.2, T.3, T.4, T.5⟩

-- the field `mean_bound` is identified by unfolding `meanOp` and the norms of `L(E)`, past the default heartbeats
set_option maxHeartbeats 4000000 in
/-- The copied `UniformMeanRegulator` to the project's, field by field. -/
def umrToP {d : ℕ} {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
    {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal} [Fact (1 ≤ r)]
    (U : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator p S η r) :
    StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP p) (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spToP S) (cpToP η) r :=
  ⟨U.1, U.2, fun R hR => csmToP (U.3 R hR), U.4, U.5, U.6, U.7, U.8, U.9, U.10, U.11, U.12⟩

set_option maxHeartbeats 4000000 in
def umrOfP {d : ℕ} {p : StratonovichHAMSecondMoment.OccupationCompletion.TParams} {S : StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
    {η : StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal} [Fact (1 ≤ r)]
    (U : StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator p S η r) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP p) (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spOfP S) (cpOfP η) r :=
  ⟨U.1, U.2, fun R hR => csmOfP (U.3 R hR), U.4, U.5, U.6, U.7, U.8, U.9, U.10, U.11, U.12⟩

end UniformMeanInterface

namespace PositiveRawMean

theorem um0ToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d) : StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d :=
  ⟨h.1, h.2, h.3, h.4⟩

theorem um0OfP {d : ℕ} (h : StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PositiveRawMean.UM0Facts d :=
  ⟨h.1, h.2, h.3, h.4⟩

end PositiveRawMean

/-! ### Wave L16 copies

The data structure `TemporalMeanCore` (field by field, both ways) and the Prop structures
`CutoffCompact`, `TemporalCompact` (whose second field quantifies over temporal mean cores) and
`SchurKernel` (field by field). -/

namespace CameronInterface

/-- The copied `TemporalMeanCore` to the project's, field by field. -/
def tmcToP {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams} {r : ENNReal} [Fact (1 ≤ r)]
    (T : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore p r) :
    StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP p) r :=
  ⟨T.1, T.2, T.3, T.4, T.5, T.6, T.7, T.8, T.9, T.10, T.11, T.12, T.13⟩

def tmcOfP {p : StratonovichHAMSecondMoment.OccupationCompletion.TParams} {r : ENNReal} [Fact (1 ≤ r)]
    (T : StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore p r) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP p) r :=
  ⟨T.1, T.2, T.3, T.4, T.5, T.6, T.7, T.8, T.9, T.10, T.11, T.12, T.13⟩

theorem ccToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.CutoffCompact d) : StratonovichHAMSecondMoment.CameronInterface.CutoffCompact d :=
  ⟨h.1⟩

theorem ccOfP {d : ℕ} (h : StratonovichHAMSecondMoment.CameronInterface.CutoffCompact d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.CutoffCompact d :=
  ⟨h.1⟩

theorem tcToP {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.TemporalCompact p) :
    StratonovichHAMSecondMoment.CameronInterface.TemporalCompact (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP p) :=
  ⟨h.1, fun r _ T => h.2 r (tmcOfP T)⟩

theorem tcOfP {p : StratonovichHAMSecondMoment.OccupationCompletion.TParams} (h : StratonovichHAMSecondMoment.CameronInterface.TemporalCompact p) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.TemporalCompact (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP p) :=
  ⟨h.1, fun r _ T => h.2 r (tmcToP T)⟩


/-- The copied `FractionalProductsTarget` (it quantifies over the copied `HomogCovariance`) to
the project's, and back. -/
theorem fptToP {d : ℕ} {alpha s : ℝ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.FractionalProductsTarget d alpha s) :
    StratonovichHAMSecondMoment.CameronInterface.FractionalProductsTarget d alpha s := by
  obtain ⟨Cs, h0, h⟩ := h
  exact ⟨Cs, h0, fun a0 Γ μ hH => h a0 Γ μ (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)⟩

theorem fptOfP {d : ℕ} {alpha s : ℝ} (h : StratonovichHAMSecondMoment.CameronInterface.FractionalProductsTarget d alpha s) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.FractionalProductsTarget d alpha s := by
  obtain ⟨Cs, h0, h⟩ := h
  exact ⟨Cs, h0, fun a0 Γ μ hH => h a0 Γ μ (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)⟩

theorem fptAllToP {d : ℕ} {alpha : ℝ}
    (h : ∀ s : ℝ, alpha / 4 < s → s < 1 / 2 → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.FractionalProductsTarget d alpha s) :
    ∀ s : ℝ, alpha / 4 < s → s < 1 / 2 → StratonovichHAMSecondMoment.CameronInterface.FractionalProductsTarget d alpha s :=
  fun s h1 h2 => fptToP (h s h1 h2)

theorem fptAllOfP {d : ℕ} {alpha : ℝ}
    (h : ∀ s : ℝ, alpha / 4 < s → s < 1 / 2 → StratonovichHAMSecondMoment.CameronInterface.FractionalProductsTarget d alpha s) :
    ∀ s : ℝ, alpha / 4 < s → s < 1 / 2 → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.FractionalProductsTarget d alpha s :=
  fun s h1 h2 => fptOfP (h s h1 h2)

/-- `UniformCutoffTarget` for every copied profile gives it for every project profile. -/
theorem uctToP {d : ℕ}
    (h : ∀ η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.UniformCutoffTarget η) :
    ∀ η : StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d, StratonovichHAMSecondMoment.CameronInterface.UniformCutoffTarget η :=
  fun η => h (StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpOfP η)

theorem uctOfP {d : ℕ}
    (h : ∀ η : StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d, StratonovichHAMSecondMoment.CameronInterface.UniformCutoffTarget η) :
    ∀ η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.UniformCutoffTarget η :=
  fun η => h (StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpToP η)

/-- The copied `CameronSpatialTarget` (it quantifies over the copied `CameronSpatialMap`). -/
theorem cstToP {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    {hH : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ}
    {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.CameronSpatialTarget hH η) :
    StratonovichHAMSecondMoment.CameronInterface.CameronSpatialTarget (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) (StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpToP η) :=
  fun R hR => let ⟨C, hC⟩ := h R hR; ⟨StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmToP C, hC⟩

theorem cstOfP {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    {hH : StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ}
    {η : StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} (h : StratonovichHAMSecondMoment.CameronInterface.CameronSpatialTarget hH η) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.CameronSpatialTarget (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) (StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpOfP η) :=
  fun R hR => let ⟨C, hC⟩ := h R hR; ⟨StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmOfP C, hC⟩

/-- The copied `TemporalMapTarget` (an existential over the copied `TemporalMeanCore`). -/
theorem tmtToP {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams} {r : ENNReal} [Fact (1 ≤ r)]
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.TemporalMapTarget p r) :
    StratonovichHAMSecondMoment.CameronInterface.TemporalMapTarget (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP p) r :=
  let ⟨T, h1, h2, h3, h4⟩ := h; ⟨tmcToP T, h1, h2, h3, h4⟩

theorem tmtOfP {p : StratonovichHAMSecondMoment.OccupationCompletion.TParams} {r : ENNReal} [Fact (1 ≤ r)]
    (h : StratonovichHAMSecondMoment.CameronInterface.TemporalMapTarget p r) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.TemporalMapTarget (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP p) r :=
  let ⟨T, h1, h2, h3, h4⟩ := h; ⟨tmcOfP T, h1, h2, h3, h4⟩

theorem netmcToP {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams} {r : ENNReal} [Fact (1 ≤ r)]
    (h : Nonempty (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore p r)) :
    Nonempty (StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP p) r) :=
  let ⟨T⟩ := h; ⟨tmcToP T⟩

theorem netmcOfP {p : StratonovichHAMSecondMoment.OccupationCompletion.TParams} {r : ENNReal} [Fact (1 ≤ r)]
    (h : Nonempty (StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore p r)) :
    Nonempty (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP p) r) :=
  let ⟨T⟩ := h; ⟨tmcOfP T⟩

/-- The copied `UMapTarget` (a universal over the copied `TemporalMeanCore`). -/
theorem umtToP {d : ℕ} {p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.TParams} {S : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
    {r : ENNReal} [Fact (1 ≤ r)] (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.UMapTarget p S r) :
    StratonovichHAMSecondMoment.CameronInterface.UMapTarget (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP p) (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spToP S) r :=
  fun T => let ⟨U, h1, h2⟩ := h (tmcOfP T); ⟨U, h1, h2⟩

theorem umtOfP {d : ℕ} {p : StratonovichHAMSecondMoment.OccupationCompletion.TParams} {S : StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
    {r : ENNReal} [Fact (1 ≤ r)] (h : StratonovichHAMSecondMoment.CameronInterface.UMapTarget p S r) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.UMapTarget (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP p) (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spOfP S) r :=
  fun T => let ⟨U, h1, h2⟩ := h (tmcToP T); ⟨U, h1, h2⟩

/-- The copied `UniformMeanRegulatorTarget` (a `Nonempty` of the copied regulator). -/
theorem umrtToP {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    {hH : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ}
    {η : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal} [Fact (1 ≤ r)]
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.UniformMeanRegulatorTarget hH η r) :
    StratonovichHAMSecondMoment.CameronInterface.UniformMeanRegulatorTarget (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) (StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpToP η) r :=
  fun h2 h3 => let ⟨U⟩ := h h2 h3; ⟨StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrToP U⟩

theorem umrtOfP {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    {hH : StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ}
    {η : StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal} [Fact (1 ≤ r)]
    (h : StratonovichHAMSecondMoment.CameronInterface.UniformMeanRegulatorTarget hH η r) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.UniformMeanRegulatorTarget (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) (StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpOfP η) r :=
  fun h2 h3 => let ⟨U⟩ := h h2 h3; ⟨StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrOfP U⟩


/-- A project regulator with the mean identity and compact values gives a copied one. -/
theorem exPrmOfP {d : ℕ} {p : StratonovichHAMSecondMoment.OccupationCompletion.TParams} {S : StratonovichHAMSecondMoment.OccupationCompletion.SpData d}
    {η : StratonovichHAMSecondMoment.UniformMeanInterface.CutoffProfile d} {r : ENNReal} [Fact (1 ≤ r)]
    (h : ∃ U : StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator p S η r,
      StratonovichHAMSecondMoment.UniformMeanInterface.PositiveRawMeanTarget U ∧ StratonovichHAMSecondMoment.CameronInterface.MeanCompactValuesTarget U) :
    ∃ U : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.UniformMeanRegulator (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP p)
        (StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spOfP S) (StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpOfP η) r,
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.PositiveRawMeanTarget U ∧ StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.MeanCompactValuesTarget U :=
  let ⟨U, h1, h2⟩ := h; ⟨StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrOfP U, h1, h2⟩

end CameronInterface

namespace CameronTemporal

theorem skToP {k : ℝ × ℝ → ℝ} {A : ℝ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronTemporal.SchurKernel k A) :
    StratonovichHAMSecondMoment.CameronTemporal.SchurKernel k A :=
  ⟨h.1, h.2, h.3, h.4⟩

theorem skOfP {k : ℝ × ℝ → ℝ} {A : ℝ} (h : StratonovichHAMSecondMoment.CameronTemporal.SchurKernel k A) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronTemporal.SchurKernel k A :=
  ⟨h.1, h.2, h.3, h.4⟩

end CameronTemporal

/-! ### Wave L17 copies

The data structures `EdgeData`, `TwoChain` and `Adm` (field by field, both ways; an edge-data
family pointwise), the Prop structures `TwoChain.WF`, `KernelHyp`, `ConvolutionNorms`,
`RegionalHalfBound`, `PairingDampedNorms.GreenDensity` and `PairingSmoothedNorms.SmoothDensity`
(field by field), and the targets whose bodies quantify over a copied structure
(`ConvolutionNormsTarget`, `CappedEnvelopeAt`, `RegionalHalfBoundTarget`,
`PairingEnvelopeTarget`, `M4BridgeTarget`). -/

namespace PairingInterface

def edToP {d : ℕ} (E : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.EdgeData d) : StratonovichHAMSecondMoment.PairingInterface.EdgeData d :=
  ⟨E.1, E.2, E.3, E.4, E.5, E.6⟩

def edOfP {d : ℕ} (E : StratonovichHAMSecondMoment.PairingInterface.EdgeData d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.EdgeData d :=
  ⟨E.1, E.2, E.3, E.4, E.5, E.6⟩

def edfToP {d : ℕ} {α : Type*} (ed : Sym2 α → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.EdgeData d) : Sym2 α → StratonovichHAMSecondMoment.PairingInterface.EdgeData d :=
  fun e => edToP (ed e)

def edfOfP {d : ℕ} {α : Type*} (ed : Sym2 α → StratonovichHAMSecondMoment.PairingInterface.EdgeData d) : Sym2 α → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.EdgeData d :=
  fun e => edOfP (ed e)

def tcToP {α : Type*} (dg : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain α) : StratonovichHAMSecondMoment.PairingInterface.TwoChain α := ⟨dg.1, dg.2, dg.3⟩

def tcOfP {α : Type*} (dg : StratonovichHAMSecondMoment.PairingInterface.TwoChain α) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain α := ⟨dg.1, dg.2, dg.3⟩

def admToP {α : Type*} [DecidableEq α] {L : Finset α} {D : Finset (Sym2 α)} (A : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.Adm L D) : StratonovichHAMSecondMoment.PairingInterface.Adm L D :=
  ⟨A.1, A.2, A.3, A.4, A.5, A.6, A.7, A.8, A.9, A.10, A.11⟩

def admOfP {α : Type*} [DecidableEq α] {L : Finset α} {D : Finset (Sym2 α)} (A : StratonovichHAMSecondMoment.PairingInterface.Adm L D) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.Adm L D :=
  ⟨A.1, A.2, A.3, A.4, A.5, A.6, A.7, A.8, A.9, A.10, A.11⟩

theorem wfToP {α : Type*} [DecidableEq α] {dg : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain α} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain.WF dg) :
    StratonovichHAMSecondMoment.PairingInterface.TwoChain.WF (tcToP dg) := ⟨h.1, h.2, h.3⟩

theorem wfOfP {α : Type*} [DecidableEq α] {dg : StratonovichHAMSecondMoment.PairingInterface.TwoChain α} (h : StratonovichHAMSecondMoment.PairingInterface.TwoChain.WF dg) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain.WF (tcOfP dg) := ⟨h.1, h.2, h.3⟩

theorem wfToP' {α : Type*} [DecidableEq α] {dg : StratonovichHAMSecondMoment.PairingInterface.TwoChain α} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain.WF (tcOfP dg)) :
    StratonovichHAMSecondMoment.PairingInterface.TwoChain.WF dg := ⟨h.1, h.2, h.3⟩

theorem wfOfP' {α : Type*} [DecidableEq α] {dg : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain α} (h : StratonovichHAMSecondMoment.PairingInterface.TwoChain.WF (tcToP dg)) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain.WF dg := ⟨h.1, h.2, h.3⟩

theorem khToP {d : ℕ} {α : Type*} [DecidableEq α] {a : ℝ} {dg : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain α}
    {ed : Sym2 α → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.EdgeData d} {G : α → StratonovichHAMSecondMoment.PairingInterface.Kernel d} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.KernelHyp a dg ed G) :
    StratonovichHAMSecondMoment.PairingInterface.KernelHyp a (tcToP dg) (edfToP ed) G := ⟨h.1, h.2, h.3, h.4⟩

theorem khOfP {d : ℕ} {α : Type*} [DecidableEq α] {a : ℝ} {dg : StratonovichHAMSecondMoment.PairingInterface.TwoChain α}
    {ed : Sym2 α → StratonovichHAMSecondMoment.PairingInterface.EdgeData d} {G : α → StratonovichHAMSecondMoment.PairingInterface.Kernel d} (h : StratonovichHAMSecondMoment.PairingInterface.KernelHyp a dg ed G) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.KernelHyp a (tcOfP dg) (edfOfP ed) G := ⟨h.1, h.2, h.3, h.4⟩

theorem cnTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.ConvolutionNormsTarget d) : StratonovichHAMSecondMoment.PairingInterface.ConvolutionNormsTarget d :=
  fun a ha ha1 G H hG hH h0G h0H =>
    let ⟨h1, h2⟩ := h a ha ha1 G H hG hH h0G h0H
    ⟨h1, fun E hE => h2 (edOfP E) hE⟩

theorem cnTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.PairingInterface.ConvolutionNormsTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.ConvolutionNormsTarget d :=
  fun a ha ha1 G H hG hH h0G h0H =>
    let ⟨h1, h2⟩ := h a ha ha1 G H hG hH h0G h0H
    ⟨h1, fun E hE => h2 (edToP E) hE⟩

theorem cnToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.ConvolutionNorms d) : StratonovichHAMSecondMoment.PairingInterface.ConvolutionNorms d := ⟨cnTToP h.1⟩

theorem cnOfP {d : ℕ} (h : StratonovichHAMSecondMoment.PairingInterface.ConvolutionNorms d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.ConvolutionNorms d := ⟨cnTOfP h.1⟩

theorem neAdmToP {α : Type*} [DecidableEq α] {L : Finset α} {D : Finset (Sym2 α)}
    (h : Nonempty (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.Adm L D)) : Nonempty (StratonovichHAMSecondMoment.PairingInterface.Adm L D) := let ⟨A⟩ := h; ⟨admToP A⟩

theorem neAdmOfP {α : Type*} [DecidableEq α] {L : Finset α} {D : Finset (Sym2 α)}
    (h : Nonempty (StratonovichHAMSecondMoment.PairingInterface.Adm L D)) : Nonempty (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.Adm L D) := let ⟨A⟩ := h; ⟨admOfP A⟩

set_option smartUnfolding false in
/-- The copied envelope is the project's at the converted diagram and edge data (the
supremum runs over the copied admissible assignments; `admToP`, `admOfP` match them). -/
theorem envC_eq {d : ℕ} {α : Type*} [DecidableEq α] (a : ℝ) (dg : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.TwoChain α)
    (ed : Sym2 α → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.EdgeData d) (G : α → StratonovichHAMSecondMoment.PairingInterface.Kernel d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.env a dg ed G = StratonovichHAMSecondMoment.PairingInterface.env a (tcToP dg) (edfToP ed) G := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.env StratonovichHAMSecondMoment.PairingInterface.env
  apply le_antisymm
  · exact iSup_le fun A => le_iSup_of_le (admToP A) le_rfl
  · exact iSup_le fun A => le_iSup_of_le (admOfP A) le_rfl

set_option smartUnfolding false in
theorem envOnC_eq {d : ℕ} {α : Type*} [DecidableEq α] (a : ℝ) (ed : Sym2 α → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.EdgeData d)
    (G : α → StratonovichHAMSecondMoment.PairingInterface.Kernel d) (L : Finset α) (D : Finset (Sym2 α)) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingRegional.envOn a ed G L D =
      StratonovichHAMSecondMoment.PairingRegional.envOn a (edfToP ed) G L D := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingRegional.envOn
    StratonovichHAMSecondMoment.PairingRegional.envOn
  apply le_antisymm
  · exact iSup_le fun A => le_iSup_of_le (admToP A) le_rfl
  · exact iSup_le fun A => le_iSup_of_le (admOfP A) le_rfl

set_option smartUnfolding false in
theorem ceaToP {d : ℕ} {α : Type*} [DecidableEq α] {a : ℝ} {n : ℕ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n) : StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n := by
  intro dg ed G hwf hn hcap hG
  have := h (tcOfP dg) (edfOfP ed) G (wfOfP hwf) hn hcap (khOfP hG)
  rw [envC_eq] at this
  exact this

set_option smartUnfolding false in
theorem ceaOfP {d : ℕ} {α : Type*} [DecidableEq α] {a : ℝ} {n : ℕ}
    (h : StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n := by
  intro dg ed G hwf hn hcap hG
  rw [envC_eq]
  exact h (tcToP dg) (edfToP ed) G (wfToP hwf) hn hcap (khToP hG)

set_option smartUnfolding false in
theorem rhbTToP {d : ℕ} {α : Type*} [DecidableEq α] {a : ℝ} {n : ℕ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBoundTarget d α a n) : StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBoundTarget d α a n := by
  intro ha ha1 hc dg ed G hwf hn hcap hG v w R hv he hR hRi hRt
  have := h ha ha1 (ceaOfP hc) (tcOfP dg) (edfOfP ed) G (wfOfP hwf) hn hcap (khOfP hG) v w R hv he
    hR hRi hRt
  rw [envC_eq] at this
  exact this

set_option smartUnfolding false in
theorem rhbTOfP {d : ℕ} {α : Type*} [DecidableEq α] {a : ℝ} {n : ℕ}
    (h : StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBoundTarget d α a n) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBoundTarget d α a n := by
  intro ha ha1 hc dg ed G hwf hn hcap hG v w R hv he hR hRi hRt
  rw [envC_eq]
  exact h ha ha1 (ceaToP hc) (tcToP dg) (edfToP ed) G (wfToP hwf) hn hcap (khToP hG) v w R hv he
    hR hRi hRt

theorem ceaAllToP {d : ℕ} {α : Type*} [DecidableEq α]
    (h : ∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n) :
    ∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n :=
  fun a ha ha1 n => ceaToP (h a ha ha1 n)

theorem ceaAllOfP {d : ℕ} {α : Type*} [DecidableEq α]
    (h : ∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n) :
    ∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n :=
  fun a ha ha1 n => ceaOfP (h a ha ha1 n)

theorem rhbAllToP {d : ℕ} {α : Type*} [DecidableEq α]
    (h : ∀ (a : ℝ) (n : ℕ), StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBoundTarget d α a n) :
    ∀ (a : ℝ) (n : ℕ), StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBoundTarget d α a n := fun a n => rhbTToP (h a n)

theorem rhbAllOfP {d : ℕ} {α : Type*} [DecidableEq α]
    (h : ∀ (a : ℝ) (n : ℕ), StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBoundTarget d α a n) :
    ∀ (a : ℝ) (n : ℕ), StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBoundTarget d α a n := fun a n => rhbTOfP (h a n)

theorem rhbToP {d : ℕ} {α : Type*} [DecidableEq α] (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBound d α) :
    StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBound d α := ⟨fun a n => rhbTToP (h.1 a n)⟩

theorem rhbOfP {d : ℕ} {α : Type*} [DecidableEq α] (h : StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBound d α) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.RegionalHalfBound d α := ⟨fun a n => rhbTOfP (h.1 a n)⟩

set_option smartUnfolding false in
theorem petToP {d : ℕ} {α : Type*} [DecidableEq α] (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d α) :
    StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d α := by
  intro a ha ha1 dg ed G hwf hG
  have := h a ha ha1 (tcOfP dg) (edfOfP ed) G (wfOfP hwf) (khOfP hG)
  rw [envC_eq] at this
  exact this

set_option smartUnfolding false in
theorem petOfP {d : ℕ} {α : Type*} [DecidableEq α] (h : StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d α) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d α := by
  intro a ha ha1 dg ed G hwf hG
  rw [envC_eq]
  exact h a ha ha1 (tcToP dg) (edfToP ed) G (wfToP hwf) (khToP hG)

theorem petAllToP {d : ℕ} (h : ∀ N : ℕ, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d (Fin N)) :
    ∀ N : ℕ, StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d (Fin N) := fun N => petToP (h N)

theorem petAllOfP {d : ℕ} (h : ∀ N : ℕ, StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d (Fin N)) :
    ∀ N : ℕ, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d (Fin N) := fun N => petOfP (h N)

theorem crToP {d : ℕ} {α : Type*} [DecidableEq α]
    (f : (∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n) →
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d α) :
    (∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n) →
      StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d α :=
  fun h => petToP (f (ceaAllOfP h))

theorem crOfP {d : ℕ} {α : Type*} [DecidableEq α]
    (f : (∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n) →
      StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d α) :
    (∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.CappedEnvelopeAt d α a n) →
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.PairingEnvelopeTarget d α :=
  fun h => petOfP (f (ceaAllToP h))

set_option smartUnfolding false in
theorem m4bToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.M4BridgeTarget d) : StratonovichHAMSecondMoment.PairingInterface.M4BridgeTarget d := by
  intro alpha α₀ Γ μ hH ε hε
  obtain ⟨E, h1, h2, h3⟩ := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) ε hε
  exact ⟨edToP E, h1, h2, h3⟩

set_option smartUnfolding false in
theorem m4bOfP {d : ℕ} (h : StratonovichHAMSecondMoment.PairingInterface.M4BridgeTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingInterface.M4BridgeTarget d := by
  intro alpha α₀ Γ μ hH ε hε
  obtain ⟨E, h1, h2, h3⟩ := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) ε hε
  exact ⟨edOfP E, h1, h2, h3⟩

end PairingInterface

namespace PairingDampedNorms

theorem gdToP {d : ℕ} {g : StratonovichHAMSecondMoment.PairingInterface.Kernel d}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingDampedNorms.GreenDensity d g) :
    StratonovichHAMSecondMoment.PairingDampedNorms.GreenDensity d g := ⟨h.1, h.2, h.3, h.4⟩

theorem gdOfP {d : ℕ} {g : StratonovichHAMSecondMoment.PairingInterface.Kernel d}
    (h : StratonovichHAMSecondMoment.PairingDampedNorms.GreenDensity d g) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingDampedNorms.GreenDensity d g := ⟨h.1, h.2, h.3, h.4⟩

end PairingDampedNorms

namespace PairingSmoothedNorms

theorem sdToP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {η : ℝ}
    {g : StratonovichHAMSecondMoment.PairingInterface.Kernel d}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingSmoothedNorms.SmoothDensity d G η g) :
    StratonovichHAMSecondMoment.PairingSmoothedNorms.SmoothDensity d G η g := ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩

theorem sdOfP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {η : ℝ}
    {g : StratonovichHAMSecondMoment.PairingInterface.Kernel d}
    (h : StratonovichHAMSecondMoment.PairingSmoothedNorms.SmoothDensity d G η g) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PairingSmoothedNorms.SmoothDensity d G η g := ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩

end PairingSmoothedNorms

/-! ### Wave L18 copies

The targets of `WickInterface` (each quantifies over the copied `HomogCovariance`; converted
through `homog_toP`/`homog_ofP`, the rest unfolds to the same terms) and the four fallback
`Prop` structures (field by field). -/

namespace WickInterface

set_option smartUnfolding false in
theorem sswTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpectralSpatialWTarget d) : StratonovichHAMSecondMoment.WickInterface.SpectralSpatialWTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem sswTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.SpectralSpatialWTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpectralSpatialWTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem splTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialPositiveLaplaceTarget d) : StratonovichHAMSecondMoment.WickInterface.SpatialPositiveLaplaceTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem splTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.SpatialPositiveLaplaceTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialPositiveLaplaceTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem slTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SmoothedLaplaceTarget d) : StratonovichHAMSecondMoment.WickInterface.SmoothedLaplaceTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem slTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.SmoothedLaplaceTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SmoothedLaplaceTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem wmbTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.WickMassBoundTarget d) : StratonovichHAMSecondMoment.WickInterface.WickMassBoundTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem wmbTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.WickMassBoundTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.WickMassBoundTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem rsTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.RhoScalingTarget d) : StratonovichHAMSecondMoment.WickInterface.RhoScalingTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem rsTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.RhoScalingTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.RhoScalingTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem m87TToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.M8M7BridgeTarget d) : StratonovichHAMSecondMoment.WickInterface.M8M7BridgeTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem m87TOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.M8M7BridgeTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.M8M7BridgeTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem swwlTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialWickWeakLimitTarget d) : StratonovichHAMSecondMoment.WickInterface.SpatialWickWeakLimitTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem swwlTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.SpatialWickWeakLimitTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialWickWeakLimitTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem swmTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialWickMeasuresTarget d) : StratonovichHAMSecondMoment.WickInterface.SpatialWickMeasuresTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem swmTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.SpatialWickMeasuresTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialWickMeasuresTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem m84TToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.M8M4IdentityTarget d) : StratonovichHAMSecondMoment.WickInterface.M8M4IdentityTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem m84TOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.M8M4IdentityTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.M8M4IdentityTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem jttTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.JointTemporalTailTarget d) : StratonovichHAMSecondMoment.WickInterface.JointTemporalTailTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem jttTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.JointTemporalTailTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.JointTemporalTailTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem jdlTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.JointDiagramLimitTarget d) : StratonovichHAMSecondMoment.WickInterface.JointDiagramLimitTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem jdlTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.JointDiagramLimitTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.JointDiagramLimitTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem dlhTToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.DiagramLimitsHomogTarget d) : StratonovichHAMSecondMoment.WickInterface.DiagramLimitsHomogTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem dlhTOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.DiagramLimitsHomogTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.DiagramLimitsHomogTarget d := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem he3TToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.HomogEnvelopeThreeTarget) : StratonovichHAMSecondMoment.WickInterface.HomogEnvelopeThreeTarget := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem he3TOfP (h : StratonovichHAMSecondMoment.WickInterface.HomogEnvelopeThreeTarget) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.HomogEnvelopeThreeTarget := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem te3TToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.ThetaEnvelopeThreeTarget) : StratonovichHAMSecondMoment.WickInterface.ThetaEnvelopeThreeTarget := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem te3TOfP (h : StratonovichHAMSecondMoment.WickInterface.ThetaEnvelopeThreeTarget) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.ThetaEnvelopeThreeTarget := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

set_option smartUnfolding false in
theorem cc3TToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.CrudeCorrectedThreeTarget) : StratonovichHAMSecondMoment.WickInterface.CrudeCorrectedThreeTarget := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)

set_option smartUnfolding false in
theorem cc3TOfP (h : StratonovichHAMSecondMoment.WickInterface.CrudeCorrectedThreeTarget) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.CrudeCorrectedThreeTarget := by
  intro alpha α₀ Γ μ hH
  exact h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)

theorem splToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialPositiveLaplace d) : StratonovichHAMSecondMoment.WickInterface.SpatialPositiveLaplace d := ⟨splTToP h.1⟩

theorem splOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.SpatialPositiveLaplace d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialPositiveLaplace d := ⟨splTOfP h.1⟩

theorem wmbToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.WickMassBound d) : StratonovichHAMSecondMoment.WickInterface.WickMassBound d := ⟨wmbTToP h.1⟩

theorem wmbOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.WickMassBound d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.WickMassBound d := ⟨wmbTOfP h.1⟩

theorem swwlToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialWickWeakLimit d) : StratonovichHAMSecondMoment.WickInterface.SpatialWickWeakLimit d := ⟨swwlTToP h.1⟩

theorem swwlOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.SpatialWickWeakLimit d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.SpatialWickWeakLimit d := ⟨swwlTOfP h.1⟩

theorem jttToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.JointTemporalTail d) : StratonovichHAMSecondMoment.WickInterface.JointTemporalTail d := ⟨jttTToP h.1⟩

theorem jttOfP {d : ℕ} (h : StratonovichHAMSecondMoment.WickInterface.JointTemporalTail d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WickInterface.JointTemporalTail d := ⟨jttTOfP h.1⟩

end WickInterface

/-! ### Wave L19 copies

The source-field objects of `SourceInterface` (model M9). `SourceField` unfolds to the copied
`Prop` structure `CenteredGaussianField` (converted by `cgfToP`/`cgfOfP`); the chain integrals
`Ya`, `YaReg` integrate against the copied chain measures, which equal the project's only by
`chainMeasure_eq`/`chainMeasureReg_eq` (built on recursive weights), so each object built on them
has an equation to the project's with the field hypothesis converted; `XL2` is defined by cases.
The targets quantify over the copied `HomogCovariance` and `SourceField`: converters both ways.
`SourceModel` (data) is rebuilt field by field. -/

namespace SourceInterface

universe u

set_option linter.unusedSimpArgs false

section Objects

variable {d : ℕ} {α₀ : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {Ω : Type*}
  [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {W : StratonovichHAMSecondMoment.SourceInterface.SrcPt d → Ω → ℝ}

theorem sfToP (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) : StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W :=
  StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP hW

theorem sfOfP (hW : StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W :=
  StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP hW

theorem Ya_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) {n : ℕ}
    (a : Fin n → StratonovichHAMSecondMoment.SourceInterface.PosW) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.Ya hW t ht x a = StratonovichHAMSecondMoment.SourceInterface.Ya (sfToP hW) t ht x a := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.Ya StratonovichHAMSecondMoment.SourceInterface.Ya
  rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickInputs.chainMeasure_eq]
  rfl

theorem YaReg_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) {n : ℕ}
    (a : Fin n → StratonovichHAMSecondMoment.SourceInterface.PosW) (η : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.YaReg hW t ht x a η = StratonovichHAMSecondMoment.SourceInterface.YaReg (sfToP hW) t ht x a η := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.YaReg StratonovichHAMSecondMoment.SourceInterface.YaReg
  rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickRegularization.chainMeasureReg_eq]
  rfl

theorem Yw_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) {n : ℕ}
    (ε δ : Fin n → ℝ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.Yw hW t ht x ε δ = StratonovichHAMSecondMoment.SourceInterface.Yw (sfToP hW) t ht x ε δ := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.Yw StratonovichHAMSecondMoment.SourceInterface.Yw
  exact Ya_eq hW t ht x _

theorem Ycom_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) (n : ℕ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.Ycom hW t ht x n = StratonovichHAMSecondMoment.SourceInterface.Ycom (sfToP hW) t ht x n := by
  funext p
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.Ycom StratonovichHAMSecondMoment.SourceInterface.Ycom
  exact Yw_eq hW t ht x _ _

theorem stratInt_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) (n : ℕ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.stratInt hW t ht x n = StratonovichHAMSecondMoment.SourceInterface.stratInt (sfToP hW) t ht x n := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.stratInt StratonovichHAMSecondMoment.SourceInterface.stratInt
  rw [Ycom_eq]

theorem XL2_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.XL2 hW t ht x = StratonovichHAMSecondMoment.SourceInterface.XL2 (sfToP hW) t ht x := by
  funext n
  cases n with
  | zero => exact Ya_eq hW t ht x _
  | succ n => exact stratInt_eq hW t ht x (n + 1)

theorem uL2_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.uL2 hW t ht x = StratonovichHAMSecondMoment.SourceInterface.uL2 (sfToP hW) t ht x := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.uL2 StratonovichHAMSecondMoment.SourceInterface.uL2
  rw [XL2_eq]

theorem srcX_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.srcX hW t ht x = StratonovichHAMSecondMoment.SourceInterface.srcX (sfToP hW) t ht x := by
  funext n
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.srcX StratonovichHAMSecondMoment.SourceInterface.srcX
  rw [XL2_eq]

theorem srcU_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.srcU hW t ht x = StratonovichHAMSecondMoment.SourceInterface.srcU (sfToP hW) t ht x := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.srcU StratonovichHAMSecondMoment.SourceInterface.srcU
  rw [uL2_eq]

end Objects

theorem srcPairing_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.srcPairing = @StratonovichHAMSecondMoment.SourceInterface.srcPairing := by
  funext d α₀ Γ t ht x m n a b D
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.srcPairing StratonovichHAMSecondMoment.SourceInterface.srcPairing
  rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickInputs.chainMeasure_eq]
  rfl

/-- The copied `SourceModel` (a data structure) rebuilt as the project's, field by field. -/
def smToP {d : ℕ} {α₀ : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (M : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceModel d α₀ Γ) : StratonovichHAMSecondMoment.SourceInterface.SourceModel d α₀ Γ :=
  @StratonovichHAMSecondMoment.SourceInterface.SourceModel.mk d α₀ Γ M.Ω M.mΩ M.P M.isProb M.W (sfToP M.field)

/-- The project's `SourceModel` rebuilt as the copy. -/
def smOfP {d : ℕ} {α₀ : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (M : StratonovichHAMSecondMoment.SourceInterface.SourceModel d α₀ Γ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceModel d α₀ Γ :=
  @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceModel.mk d α₀ Γ M.Ω M.mΩ M.P M.isProb M.W (sfOfP M.field)

set_option smartUnfolding false in
theorem twwToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.TerminalWickWTarget.{u} d) : StratonovichHAMSecondMoment.SourceInterface.TerminalWickWTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (sfOfP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem twwOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.TerminalWickWTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.TerminalWickWTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (sfToP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem tmmToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.TerminalMixedMomentTarget.{u} d) : StratonovichHAMSecondMoment.SourceInterface.TerminalMixedMomentTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (sfOfP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem tmmOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.TerminalMixedMomentTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.TerminalMixedMomentTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (sfToP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem fol2ToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.FixedOrderL2Target.{u} d) : StratonovichHAMSecondMoment.SourceInterface.FixedOrderL2Target.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (sfOfP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem fol2OfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.FixedOrderL2Target.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.FixedOrderL2Target.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (sfToP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem gfToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.GreenFirstTarget.{u} d) : StratonovichHAMSecondMoment.SourceInterface.GreenFirstTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (sfOfP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem gfOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.GreenFirstTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.GreenFirstTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (sfToP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem exl2ToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.ExpansionL2Target.{u} d) : StratonovichHAMSecondMoment.SourceInterface.ExpansionL2Target.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (sfOfP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem exl2OfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.ExpansionL2Target.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.ExpansionL2Target.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (sfToP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem mtToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.MixedTermsTarget.{u} d) : StratonovichHAMSecondMoment.SourceInterface.MixedTermsTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (sfOfP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem mtOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.MixedTermsTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.MixedTermsTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (sfToP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem fmsToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.FirstMomentSeriesTarget.{u} d) : StratonovichHAMSecondMoment.SourceInterface.FirstMomentSeriesTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (sfOfP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem fmsOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.FirstMomentSeriesTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.FirstMomentSeriesTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (sfToP hW)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem sccToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceCovContinuousTarget d) : StratonovichHAMSecondMoment.SourceInterface.SourceCovContinuousTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem sccOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.SourceCovContinuousTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceCovContinuousTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem trvToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.TerminalReversalTarget d) : StratonovichHAMSecondMoment.SourceInterface.TerminalReversalTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem trvOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.TerminalReversalTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.TerminalReversalTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem dliToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.DiagramLimIdentTarget d) : StratonovichHAMSecondMoment.SourceInterface.DiagramLimIdentTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem dliOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.DiagramLimIdentTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.DiagramLimIdentTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem vdToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.VertexDiagramTarget d) : StratonovichHAMSecondMoment.SourceInterface.VertexDiagramTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem vdOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.VertexDiagramTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.VertexDiagramTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

set_option smartUnfolding false in
theorem sftToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceFeatureTarget d) : StratonovichHAMSecondMoment.SourceInterface.SourceFeatureTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem sftOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.SourceFeatureTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceFeatureTarget d := by
  intro alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
  exact h'

theorem isoToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.IsonormalTarget) : StratonovichHAMSecondMoment.SourceInterface.IsonormalTarget := by
  intro H _ _ _
  obtain ⟨Ω, m, Q, V, h1, h2⟩ := h H
  exact ⟨Ω, m, Q, V, h1, StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP h2⟩

theorem isoOfP (h : StratonovichHAMSecondMoment.SourceInterface.IsonormalTarget) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.IsonormalTarget := by
  intro H _ _ _
  obtain ⟨Ω, m, Q, V, h1, h2⟩ := h H
  exact ⟨Ω, m, Q, V, h1, StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP h2⟩

theorem sftgToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceFieldTarget d) : StratonovichHAMSecondMoment.SourceInterface.SourceFieldTarget d := by
  intro alpha α₀ Γ μ hH
  exact (h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)).map smToP

theorem sftgOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.SourceFieldTarget d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceFieldTarget d := by
  intro alpha α₀ Γ μ hH
  exact (h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)).map smOfP

set_option smartUnfolding false in
theorem vcToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.VertexCrudeTarget.{u} d) : StratonovichHAMSecondMoment.SourceInterface.VertexCrudeTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨Cc, θ₀, hC, hθ, h1, h2, h3⟩ := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  refine ⟨Cc, θ₀, hC, hθ, fun P _ W hW t ht x n hn a => ?_, fun P _ W hW t ht x n => ?_, h3⟩
  · have h' := h1 P W (sfOfP hW) t ht x n hn a
    try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
    exact h'
  · have h' := h2 P W (sfOfP hW) t ht x n
    try simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq] at h'
    exact h'

set_option smartUnfolding false in
theorem vcOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.VertexCrudeTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.VertexCrudeTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨Cc, θ₀, hC, hθ, h1, h2, h3⟩ := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  refine ⟨Cc, θ₀, hC, hθ, fun P _ W hW t ht x n hn a => ?_, fun P _ W hW t ht x n => ?_, h3⟩
  · have h' := h1 P W (sfToP hW) t ht x n hn a
    simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
    exact h'
  · have h' := h2 P W (sfToP hW) t ht x n
    simp only [Ya_eq, YaReg_eq, Yw_eq, Ycom_eq, stratInt_eq, XL2_eq, uL2_eq, srcX_eq, srcU_eq, srcPairing_eq]
    exact h'

theorem snToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceNoise d) : StratonovichHAMSecondMoment.SourceInterface.SourceNoise d := ⟨sftgToP h.holds⟩
theorem snOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.SourceNoise d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceNoise d := ⟨sftgOfP h.holds⟩
theorem trToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.TerminalReversal d) : StratonovichHAMSecondMoment.SourceInterface.TerminalReversal d := ⟨trvToP h.holds⟩
theorem trOfP {d : ℕ} (h : StratonovichHAMSecondMoment.SourceInterface.TerminalReversal d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.TerminalReversal d := ⟨trvOfP h.holds⟩

end SourceInterface

/-- Rewrite every copy that is not equal to the project's definition by unfolding. -/
macro "bridge_rw" : tactic =>
  `(tactic| repeat (first
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalDilation.integratedRate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalDilation.rate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rayleighRate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rayleighSet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rt_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.chainState_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tci_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.scoreSet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.score1Set_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.testRadius_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.S1Bdd_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.S1pos_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialStaticControls.lamSq_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialStaticControls.lam_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialStaticControls.lamZ_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialStaticControls.rayleighFloor_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialSmoothRatio.staticControls_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.kernelEntry_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.maskedKernel_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.kernelLp_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.inputBound_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.outputBound_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.coef_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.kerH_eq]
    | simp only [StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.envC_eq, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.envOnC_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twi_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spb_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.EstarO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.energySet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occ_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gf_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcs_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcs_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgf_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.orderedProd_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainWeight_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainWeightReal_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainMass_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainMassReal_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gm_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RemoveMask.maskedRate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RemoveMask.maskedIntegratedRate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RemoveMask.rawBlock_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialBracket.occK0_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pc_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RawOccupationEnergy.ratioSet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RawOccupationEnergy.Cocc_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RawOccupationEnergy.energySet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RawOccupationEnergy.EO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FixedSplit.SplitInputs_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FixedSplit.word_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FixedSplit.wordSeq_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FiniteWordCutoff.duhamelWords_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FiniteWordCutoff.cutWordC_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FiniteWordCutoff.counts_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FiniteWordCutoff.raw_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FiniteWordCutoff.cut_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickRegularization.chainMeasureReg_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickRegularization.noiseMeasure_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickInputs.chainMeasure_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickInputs.chainMeasureRaw_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickInputs.timeMeasure_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.blockIter_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpi_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.EstarClassO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.CoccO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.EOO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.energySetO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.ratioSetO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.rawEnergySetO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.good_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ep_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ic_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.pp_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.co_eq]))

/-- `bridge_exact d [c₁, …]` introduces every binder of the goal and closes it with the
constant `d` applied to the introduced variables, in order: each variable is passed as it
is when its type matches `d`'s binder up to unfolding, else through the first converter
`cᵢ` (a function from a copied structure or predicate to the project's) that makes it
match; the result is accepted as it is or through a converter back. It builds an
ordinary proof term, checked by the kernel; it fails when no match is found. -/
syntax (name := bridgeExact) "bridge_exact " ident " [" ident,* "]" : tactic

open Lean Meta Elab Tactic in
@[tactic bridgeExact] def evalBridgeExact : Tactic := fun stx => do
  let d := stx[1]
  let cs := stx[3].getSepArgs
  let g ← getMainGoal
  let (xs, g) ← g.intros
  g.withContext do
    let f ← mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverload d)
    let convs ← cs.mapM fun c => realizeGlobalConstNoOverload c
    let conv (x : Expr) (target : Expr) : MetaM (Option Expr) := do
      if ← isDefEq (← inferType x) target then return some x
      for c in convs do
        let some a ← observing? (mkAppM c #[x]) | continue
        if ← isDefEq (← inferType a) target then return some a
      return none
    let mut e := f
    let mut ty ← inferType f
    for xv in xs do
      let x := mkFVar xv
      ty ← whnf ty
      let .forallE _ dom body _ := ty
        | throwError "bridge_exact: {d} has fewer binders than the goal"
      let some a ← conv x dom
        | throwError "bridge_exact: no conversion of {x} : {← inferType x} to {dom}"
      e := mkApp e a
      ty := body.instantiate1 a
    let goalTy ← g.getType
    let some r ← conv e goalTy
      | throwError "bridge_exact: result {ty} does not match the goal {goalTy}"
    let r ← instantiateMVars r
    if r.hasExprMVar then throwError "bridge_exact: unassigned metavariables remain"
    g.assign r

/-- `bridge_exact` with every converter of this file. -/
macro "bridge_auto " d:ident : tactic =>
  `(tactic| (bridge_rw; bridge_exact $d [StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gToP, StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cToP,
      StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rtToP, StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP, StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.toP,
      StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gOfP, StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cOfP, StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rtOfP,
      StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP,
      StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmToP, StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciToP, StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiToP, StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfToP, StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP, StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdToP, StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP, StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiToP, StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FockColumnBound.l2ToP, StratonovichHamSecondMomentLeanAuditBridge.FockColumnBound.l2OfP,
      StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.goodToP, StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.goodOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.icToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.icOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.epToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.epOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ppToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ppOfP,
      StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.coToP, StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.coOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spOfP,
StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PositiveRawMean.um0ToP, StratonovichHamSecondMomentLeanAuditBridge.PositiveRawMean.um0OfP,
            StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.ccToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.ccOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronTemporal.skToP, StratonovichHamSecondMomentLeanAuditBridge.CameronTemporal.skOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptAllToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptAllOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.uctToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.uctOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.cstToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.cstOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmtOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.netmcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.netmcOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umtOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umrtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umrtOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.exPrmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cxToP, StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cxOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edfToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edfOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.tcToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.tcOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.admToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.admOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.neAdmToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.neAdmOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfToP', StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfOfP', StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.khToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.khOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnTToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnTOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbTToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbTOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.crToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.crOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.m4bToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.m4bOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingDampedNorms.gdToP, StratonovichHamSecondMomentLeanAuditBridge.PairingDampedNorms.gdOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingSmoothedNorms.sdToP, StratonovichHamSecondMomentLeanAuditBridge.PairingSmoothedNorms.sdOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.sswTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.sswTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.slTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.slTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.rsTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.rsTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m87TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m87TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swmTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swmTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m84TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m84TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jdlTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jdlTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.dlhTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.dlhTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.he3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.he3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.te3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.te3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.cc3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.cc3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttOfP]))

/-- Revert every local hypothesis of the goal (in context order), so that a statement
written with binders before the colon can be closed by `bridge_auto`. -/
elab "bridge_revert_all" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let fvs ← g.withContext do
    let lctx ← Lean.getLCtx
    return lctx.getFVarIds.filter fun f => !(lctx.get! f).isImplementationDetail
  let (_, g) ← g.revert fvs (preserveOrder := true)
  Lean.Elab.Tactic.replaceMainGoal [g]

/-- `bridge_cases d [c₁, …]`: as `bridge_exact`, but after introducing the binders it
splits every variable whose type is the copied inductive `Wave`, `Trig` or `Component` into its
constructors (the copies then unfold to the project's terms), and closes each case with
`d` applied to the introduced variables, a split variable replaced by its constructor
passed through the converters. It builds an ordinary proof term, checked by the kernel. -/
syntax (name := bridgeCases) "bridge_cases " ident " [" ident,* "]" : tactic

open Lean Meta Elab Tactic in
@[tactic bridgeCases] def evalBridgeCases : Tactic := fun stx => do
  let d := stx[1]
  let cs := stx[3].getSepArgs
  let g ← getMainGoal
  let (xs, g) ← g.intros
  let isSplit (t : Expr) : MetaM Bool := do
    let t ← whnf t
    match t.getAppFn with
    | .const n _ => return n == ``StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave
        || n == ``StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig
        || n == ``StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointCorollaries.Component
    | _ => return false
  -- the goals with, for each, the expressions standing for `xs`
  let mut work : Array (MVarId × Array Expr) := #[(g, xs.map mkFVar)]
  let mut done : Array (MVarId × Array Expr) := #[]
  while h : work.size > 0 do
    let (g, es) := work.back
    work := work.pop
    let next? ← g.withContext do
      es.findM? fun e => do return e.isFVar && (← isSplit (← inferType e))
    match next? with
    | none => done := done.push (g, es)
    | some e =>
      let subs ← g.cases e.fvarId!
      for sg in subs do
        work := work.push (sg.mvarId, es.map fun x => sg.subst.apply x)
  let f0 ← realizeGlobalConstNoOverload d
  let convs ← cs.mapM fun c => realizeGlobalConstNoOverload c
  for (g, es) in done do
    g.withContext do
      let conv (x : Expr) (target : Expr) : MetaM (Option Expr) := do
        if ← isDefEq (← inferType x) target then return some x
        for c in convs do
          let some a ← observing? (mkAppM c #[x]) | continue
          if ← isDefEq (← inferType a) target then return some a
        return none
      let mut e ← mkConstWithFreshMVarLevels f0
      let mut ty ← inferType e
      for x in es do
        ty ← whnf ty
        let .forallE _ dom body _ := ty
          | throwError "bridge_cases: {d} has fewer binders than the goal"
        let some a ← conv x dom
          | throwError "bridge_cases: no conversion of {x} : {← inferType x} to {dom}"
        e := mkApp e a
        ty := body.instantiate1 a
      let goalTy ← g.getType
      let some r ← conv e goalTy
        | throwError "bridge_cases: result {ty} does not match the goal {goalTy}"
      let r ← instantiateMVars r
      if r.hasExprMVar then throwError "bridge_cases: unassigned metavariables remain"
      g.assign r
  replaceMainGoal []

/-- `bridge_cases` with every converter of this file. -/
macro "bridge_cases_auto " d:ident : tactic =>
  `(tactic| (bridge_rw; bridge_cases $d [StratonovichHamSecondMomentLeanAuditBridge.MaskedContinuousWave.toP,
      StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.toP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.compToP,
      StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP, StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmToP, StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciToP, StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiToP, StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfToP, StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP, StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdToP, StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP, StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiToP, StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FockColumnBound.l2ToP, StratonovichHamSecondMomentLeanAuditBridge.FockColumnBound.l2OfP,
      StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.goodToP, StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.goodOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.icToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.icOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.epToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.epOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ppToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ppOfP,
      StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.coToP, StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.coOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spOfP,
StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PositiveRawMean.um0ToP, StratonovichHamSecondMomentLeanAuditBridge.PositiveRawMean.um0OfP,
            StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.ccToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.ccOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronTemporal.skToP, StratonovichHamSecondMomentLeanAuditBridge.CameronTemporal.skOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptAllToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptAllOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.uctToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.uctOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.cstToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.cstOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmtOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.netmcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.netmcOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umtOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umrtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umrtOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.exPrmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cxToP, StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cxOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edfToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edfOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.tcToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.tcOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.admToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.admOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.neAdmToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.neAdmOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfToP', StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfOfP', StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.khToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.khOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnTToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnTOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbTToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbTOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.crToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.crOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.m4bToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.m4bOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingDampedNorms.gdToP, StratonovichHamSecondMomentLeanAuditBridge.PairingDampedNorms.gdOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingSmoothedNorms.sdToP, StratonovichHamSecondMomentLeanAuditBridge.PairingSmoothedNorms.sdOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.sswTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.sswTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.slTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.slTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.rsTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.rsTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m87TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m87TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swmTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swmTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m84TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m84TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jdlTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jdlTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.dlhTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.dlhTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.he3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.he3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.te3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.te3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.cc3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.cc3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttOfP]))

/-- `bridge_auto` for wave L19: the equations of the source-field objects first (`simp only`,
under binders), then `bridge_exact` with every converter of this file and the wave-L19 ones. -/
macro "bridge_auto19 " d:ident : tactic =>
  `(tactic| (bridge_rw; (try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq]); bridge_exact $d [StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gToP, StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cToP,
      StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rtToP, StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP, StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.toP,
      StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gOfP, StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cOfP, StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rtOfP,
      StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP,
      StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmToP, StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciToP, StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiToP, StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfToP, StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP, StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdToP, StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP, StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiToP, StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FockColumnBound.l2ToP, StratonovichHamSecondMomentLeanAuditBridge.FockColumnBound.l2OfP,
      StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.goodToP, StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.goodOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.icToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.icOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.epToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.epOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ppToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ppOfP,
      StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.coToP, StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.coOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spOfP,
StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PositiveRawMean.um0ToP, StratonovichHamSecondMomentLeanAuditBridge.PositiveRawMean.um0OfP,
            StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.ccToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.ccOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronTemporal.skToP, StratonovichHamSecondMomentLeanAuditBridge.CameronTemporal.skOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptAllToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptAllOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.uctToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.uctOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.cstToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.cstOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmtOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.netmcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.netmcOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umtOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umrtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umrtOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.exPrmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cxToP, StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cxOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edfToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edfOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.tcToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.tcOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.admToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.admOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.neAdmToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.neAdmOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfToP', StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfOfP', StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.khToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.khOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnTToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnTOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbTToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbTOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.crToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.crOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.m4bToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.m4bOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingDampedNorms.gdToP, StratonovichHamSecondMomentLeanAuditBridge.PairingDampedNorms.gdOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingSmoothedNorms.sdToP, StratonovichHamSecondMomentLeanAuditBridge.PairingSmoothedNorms.sdOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.sswTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.sswTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.slTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.slTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.rsTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.rsTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m87TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m87TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swmTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swmTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m84TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m84TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jdlTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jdlTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.dlhTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.dlhTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.he3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.he3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.te3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.te3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.cc3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.cc3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.twwToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.twwOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.tmmToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.tmmOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.fol2ToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.fol2OfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.gfToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.gfOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.exl2ToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.exl2OfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.mtToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.mtOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.fmsToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.fmsOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sccToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sccOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.trvToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.trvOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.dliToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.dliOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.vdToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.vdOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sftToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sftOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.isoToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.isoOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sftgToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sftgOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.vcToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.vcOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.snToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.snOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.trToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.trOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.smToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.smOfP]))

/-! ### Wave L20 copies

The mild-construction objects of `MildInterface`. The polynomial spaces `polyGen`, `PolyLE`,
`LinG` and the field objects `Wa` (field values) are equal to the project's with the field
hypothesis converted (`cgfToP`, `sfToP`; a `Prop` structure, so by proof irrelevance); `Yf`,
`Xf`, `uf` rewrite through L19's `Ya_eq`, `XL2_eq`, `uL2_eq`; the mild measures integrate the
copied chain measures, equal to the project's only by `chainMeasure_eq`/`chainMeasureReg_eq`,
so `mildMeasure`, `mildMeasureReg`, `mildInt`, `mildIntReg`, `Ina`, `Ia` and `firstMean` get
equations. The targets quantify over the copied `HomogCovariance`, `SourceField` and
`CenteredGaussianField`: converters both ways. -/

namespace MildInterface

universe u v

set_option linter.unusedSimpArgs false

section Poly

variable {X : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}

theorem polyGen_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P) (n : ℕ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.polyGen hW n = StratonovichHAMSecondMoment.MildInterface.polyGen (StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP hW) n := rfl

theorem PolyLE_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P) (n : ℕ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.PolyLE hW n = StratonovichHAMSecondMoment.MildInterface.PolyLE (StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP hW) n := rfl

theorem LinG_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.LinG hW = StratonovichHAMSecondMoment.MildInterface.LinG (StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP hW) := rfl

end Poly

section Fields

variable {d : ℕ} {α₀ : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {Ω : Type*}
  [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {W : StratonovichHAMSecondMoment.SourceInterface.SrcPt d → Ω → ℝ}

theorem Wa_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (a : StratonovichHAMSecondMoment.SourceInterface.PosW) (p : ℝ × StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Wa hW a p = StratonovichHAMSecondMoment.MildInterface.Wa (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) a p := rfl

theorem Yf_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) {n : ℕ} (b : Fin n → StratonovichHAMSecondMoment.SourceInterface.PosW) (p : ℝ × StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Yf hW b p = StratonovichHAMSecondMoment.MildInterface.Yf (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) b p := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Yf StratonovichHAMSecondMoment.MildInterface.Yf
  by_cases h : 0 ≤ p.1
  · simp only [h, dif_pos, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq]
  · simp only [h, dif_neg, not_false_eq_true]

theorem Xf_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (n : ℕ) (p : ℝ × StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Xf hW n p = StratonovichHAMSecondMoment.MildInterface.Xf (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) n p := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Xf StratonovichHAMSecondMoment.MildInterface.Xf
  by_cases h : 0 ≤ p.1
  · simp only [h, dif_pos, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq]
  · simp only [h, dif_neg, not_false_eq_true]

theorem uf_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (p : ℝ × StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.uf hW p = StratonovichHAMSecondMoment.MildInterface.uf (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) p := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.uf StratonovichHAMSecondMoment.MildInterface.uf
  by_cases h : 0 ≤ p.1
  · simp only [h, dif_pos, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq]
  · simp only [h, dif_neg, not_false_eq_true]

end Fields

theorem mildMeasure_eq (d : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.mildMeasure d t ht x = StratonovichHAMSecondMoment.MildInterface.mildMeasure d t ht x := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.mildMeasure StratonovichHAMSecondMoment.MildInterface.mildMeasure
  rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickInputs.chainMeasure_eq]
  rfl

theorem mildMeasureReg_eq (d : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) (η : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.mildMeasureReg d t ht x η = StratonovichHAMSecondMoment.MildInterface.mildMeasureReg d t ht x η := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.mildMeasureReg StratonovichHAMSecondMoment.MildInterface.mildMeasureReg
  rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWickRegularization.chainMeasureReg_eq]
  rfl

section Ints

variable {d : ℕ} {α₀ : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {Ω : Type*}
  [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {W : StratonovichHAMSecondMoment.SourceInterface.SrcPt d → Ω → ℝ}

theorem mildInt_eq (f : ℝ × StratonovichHAMSecondMoment.HomogHypothesis.Rd d → MeasureTheory.Lp ℝ 2 P) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.mildInt f t ht x = StratonovichHAMSecondMoment.MildInterface.mildInt f t ht x := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.mildInt StratonovichHAMSecondMoment.MildInterface.mildInt
  rw [mildMeasure_eq]

theorem mildIntReg_eq (f : ℝ × StratonovichHAMSecondMoment.HomogHypothesis.Rd d → MeasureTheory.Lp ℝ 2 P) (t : ℝ) (ht : 0 ≤ t) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d)
    (η : ℝ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.mildIntReg f t ht x η = StratonovichHAMSecondMoment.MildInterface.mildIntReg f t ht x η := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.mildIntReg StratonovichHAMSecondMoment.MildInterface.mildIntReg
  rw [mildMeasureReg_eq]

theorem Ina_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (a : StratonovichHAMSecondMoment.SourceInterface.PosW) (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Ina hW a n t ht x = StratonovichHAMSecondMoment.MildInterface.Ina (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) a n t ht x := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Ina StratonovichHAMSecondMoment.MildInterface.Ina
  rw [mildInt_eq]
  simp only [Xf_eq]
  rfl

theorem Ia_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (a : StratonovichHAMSecondMoment.SourceInterface.PosW) (t : ℝ) (ht : 0 ≤ t)
    (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Ia hW a t ht x = StratonovichHAMSecondMoment.MildInterface.Ia (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) a t ht x := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.Ia StratonovichHAMSecondMoment.MildInterface.Ia
  rw [mildInt_eq]
  simp only [uf_eq]
  rfl

theorem firstMean_eq (hW : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.SourceField α₀ Γ P W) (x : StratonovichHAMSecondMoment.HomogHypothesis.Rd d) (t : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.firstMean hW x t = StratonovichHAMSecondMoment.MildInterface.firstMean (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) x t := by
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.firstMean StratonovichHAMSecondMoment.MildInterface.firstMean
  by_cases h : 0 < t
  · simp only [h, dif_pos, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq]
  · simp only [h, dif_neg, not_false_eq_true]

end Ints

set_option smartUnfolding false in
theorem pmToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.PolyMemTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.PolyMemTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem pmOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.PolyMemTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.PolyMemTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem jmToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.JointMeasTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.JointMeasTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem jmOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.JointMeasTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.JointMeasTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem fcToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FieldContTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.FieldContTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem fcOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.FieldContTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FieldContTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem tfToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.TerminalFubiniTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.TerminalFubiniTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem tfOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.TerminalFubiniTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.TerminalFubiniTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem gwToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.GreenWidthMildTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.GreenWidthMildTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem gwOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.GreenWidthMildTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.GreenWidthMildTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem evToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.ExternalVertexTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.ExternalVertexTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem evOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.ExternalVertexTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.ExternalVertexTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem mcToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.MildConstructionTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.MildConstructionTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem mcOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.MildConstructionTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.MildConstructionTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem omToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.OccupiedMultTarget.{u, v}) : StratonovichHAMSecondMoment.MildInterface.OccupiedMultTarget.{u, v} := by
  intro X Ω _ P _ W K hW
  have h' := h P W K (StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem omOfP (h : StratonovichHAMSecondMoment.MildInterface.OccupiedMultTarget.{u, v}) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.OccupiedMultTarget.{u, v} := by
  intro X Ω _ P _ W K hW
  have h' := h P W K (StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem duwToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.D1UpperWhiteTarget.{u}) : StratonovichHAMSecondMoment.MildInterface.D1UpperWhiteTarget.{u} := by
  intro c α₀ t h0 h1 hc ht Ω _ P _ W hW x
  have h' := h h0 h1 hc ht (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem duwOfP (h : StratonovichHAMSecondMoment.MildInterface.D1UpperWhiteTarget.{u}) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.D1UpperWhiteTarget.{u} := by
  intro c α₀ t h0 h1 hc ht Ω _ P _ W hW x
  have h' := h h0 h1 hc ht (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem durToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.D1UpperRieszTarget.{u}) : StratonovichHAMSecondMoment.MildInterface.D1UpperRieszTarget.{u} := by
  intro c α α₀ t h0 h1 hc ha ha1 ht Ω _ P _ W hW x
  have h' := h h0 h1 hc ha ha1 ht (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem durOfP (h : StratonovichHAMSecondMoment.MildInterface.D1UpperRieszTarget.{u}) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.D1UpperRieszTarget.{u} := by
  intro c α α₀ t h0 h1 hc ha ha1 ht Ω _ P _ W hW x
  have h' := h h0 h1 hc ha ha1 ht (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem rsToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.RieszSmallTarget.{u}) : StratonovichHAMSecondMoment.MildInterface.RieszSmallTarget.{u} := by
  intro c α α₀ hc ha ha1 h0 h1 Ω _ P _ W hW t ht x
  have h' := h hc ha ha1 h0 h1 (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) ht x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem rsOfP (h : StratonovichHAMSecondMoment.MildInterface.RieszSmallTarget.{u}) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.RieszSmallTarget.{u} := by
  intro c α α₀ hc ha ha1 h0 h1 Ω _ P _ W hW t ht x
  have h' := h hc ha ha1 h0 h1 (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) ht x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem fcrToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRieszTarget.{u}) : StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRieszTarget.{u} := by
  intro c α α₀ hc ha ha1 h0 h1 Ω _ P _ W hW t ht x
  have h' := h hc ha ha1 h0 h1 (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) ht x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem fcrOfP (h : StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRieszTarget.{u}) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRieszTarget.{u} := by
  intro c α α₀ hc ha ha1 h0 h1 Ω _ P _ W hW t ht x
  have h' := h hc ha ha1 h0 h1 (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) ht x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem frtToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateTarget.{u} d := by
  intro α α₀ Γ μ hH ha hV Ω _ P _ W hW x L
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) ha hV (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) x L
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem frtOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateTarget.{u} d := by
  intro α α₀ Γ μ hH ha hV Ω _ P _ W hW x L
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) ha hV (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) x L
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem frwToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateWhiteTarget.{u}) : StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateWhiteTarget.{u} := by
  intro c α₀ hc h0 h1 Ω _ P _ W hW x L
  have h' := h hc h0 h1 (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) x L
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem frwOfP (h : StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateWhiteTarget.{u}) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateWhiteTarget.{u} := by
  intro c α₀ hc h0 h1 Ω _ P _ W hW x L
  have h' := h hc h0 h1 (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) x L
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem frrToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateRieszTarget.{u}) : StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateRieszTarget.{u} := by
  intro c α α₀ hc ha ha1 h0 h1 Ω _ P _ W hW x L
  have h' := h hc ha ha1 h0 h1 (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) x L
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem frrOfP (h : StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateRieszTarget.{u}) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FirstCalibrationRateRieszTarget.{u} := by
  intro c α α₀ hc ha ha1 h0 h1 Ω _ P _ W hW x L
  have h' := h hc ha ha1 h0 h1 (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) x L
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem lauToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.LowAlphaUpperTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.LowAlphaUpperTarget.{u} d := by
  intro α α₀ Γ μ hH ha hV Ω _ P _ W hW t ht x
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH) ha hV (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) ht x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem lauOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.LowAlphaUpperTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.LowAlphaUpperTarget.{u} d := by
  intro α α₀ Γ μ hH ha hV Ω _ P _ W hW t ht x
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) ha hV (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) ht x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem rkToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.RhoGtKappaTarget) : StratonovichHAMSecondMoment.MildInterface.RhoGtKappaTarget := by
  intro d alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem rkOfP (h : StratonovichHAMSecondMoment.MildInterface.RhoGtKappaTarget) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.RhoGtKappaTarget := by
  intro d alpha α₀ Γ μ hH
  have h' := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

theorem fmToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FieldMeasTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.FieldMeasTarget.{u} d :=
  ⟨jmToP h.1, fcToP h.2⟩

theorem fmOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.FieldMeasTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.FieldMeasTarget.{u} d :=
  ⟨jmOfP h.1, fcOfP h.2⟩

theorem jmiToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.JointMeasurability.{u} d) : StratonovichHAMSecondMoment.MildInterface.JointMeasurability.{u} d :=
  ⟨jmToP h.holds⟩

theorem jmiOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.JointMeasurability.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.JointMeasurability.{u} d :=
  ⟨jmOfP h.holds⟩

theorem tfiToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.TerminalFubini.{u} d) : StratonovichHAMSecondMoment.MildInterface.TerminalFubini.{u} d :=
  ⟨tfToP h.holds⟩

theorem tfiOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.TerminalFubini.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.TerminalFubini.{u} d :=
  ⟨tfOfP h.holds⟩

theorem riToP (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.RieszInstanceTarget) : StratonovichHAMSecondMoment.MildInterface.RieszInstanceTarget := by
  intro c α α₀ h0 h1 hc ha ha1
  obtain ⟨μ, hμ⟩ := h h0 h1 hc ha ha1
  exact ⟨μ, StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hμ⟩

theorem riOfP (h : StratonovichHAMSecondMoment.MildInterface.RieszInstanceTarget) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.RieszInstanceTarget := by
  intro c α α₀ h0 h1 hc ha ha1
  obtain ⟨μ, hμ⟩ := h h0 h1 hc ha ha1
  exact ⟨μ, StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hμ⟩

set_option smartUnfolding false in
theorem pvToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.PartialVertexTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.PartialVertexTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨Cc, θ₀, hC, hθ, h1⟩ := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  refine ⟨Cc, θ₀, hC, hθ, fun {Ω} _ P _ W hW => ?_⟩
  have h' := h1 P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem pvOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.PartialVertexTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.PartialVertexTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨Cc, θ₀, hC, hθ, h1⟩ := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  refine ⟨Cc, θ₀, hC, hθ, fun {Ω} _ P _ W hW => ?_⟩
  have h' := h1 P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW)
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

set_option smartUnfolding false in
theorem envToP {d : ℕ} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.EnvelopeTarget.{u} d) : StratonovichHAMSecondMoment.MildInterface.EnvelopeTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨K, hK, h1, h2, h3⟩ := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP hH)
  refine ⟨K, hK, fun t ht {Ω} _ P _ W hW x => ?_, h2, h3⟩
  have h' := h1 t ht P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP hW) x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq] at h'
  exact h'

set_option smartUnfolding false in
theorem envOfP {d : ℕ} (h : StratonovichHAMSecondMoment.MildInterface.EnvelopeTarget.{u} d) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.EnvelopeTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨K, hK, h1, h2, h3⟩ := h (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH)
  refine ⟨K, hK, fun t ht {Ω} _ P _ W hW x => ?_, h2, h3⟩
  have h' := h1 t ht P W (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP hW) x
  try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq]
  exact h'

end MildInterface

set_option maxRecDepth 20000 in
/-- `bridge_auto` for wave L20: the equations of the L19 source-field objects and of the L20
mild-construction objects first (`simp only`, under binders), then `bridge_exact` with every
converter of this file and the wave-L19 and wave-L20 ones. -/
macro "bridge_auto20 " d:ident : tactic =>
  `(tactic| (bridge_rw; (try simp only [StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ya_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.YaReg_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Yw_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.Ycom_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.stratInt_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.XL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcX_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcU_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.srcPairing_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Yf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Xf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.uf_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasure_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildMeasureReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildIntReg_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mildInt_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ina_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.firstMean_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.PolyLE_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.LinG_eq, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.polyGen_eq]); bridge_exact $d [StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gToP, StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cToP,
      StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rtToP, StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP, StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.toP,
      StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gOfP, StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cOfP, StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rtOfP,
      StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP,
      StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmToP, StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciToP, StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiToP, StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfToP, StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP, StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdToP, StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP, StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiToP, StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FockColumnBound.l2ToP, StratonovichHamSecondMomentLeanAuditBridge.FockColumnBound.l2OfP,
      StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.goodToP, StratonovichHamSecondMomentLeanAuditBridge.VariationalMeanDerivatives.goodOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.icToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.icOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.epToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.epOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ppToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointLemmas.ppOfP,
      StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.coToP, StratonovichHamSecondMomentLeanAuditBridge.ClassOBridge.coOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCompletion.spOfP,
StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.cpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.csmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrToP, StratonovichHamSecondMomentLeanAuditBridge.UniformMeanInterface.umrOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PositiveRawMean.um0ToP, StratonovichHamSecondMomentLeanAuditBridge.PositiveRawMean.um0OfP,
            StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.tmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttToP, StratonovichHamSecondMomentLeanAuditBridge.EndpointCorollaries.ttOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.ccToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.ccOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tcOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronTemporal.skToP, StratonovichHamSecondMomentLeanAuditBridge.CameronTemporal.skOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptAllToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.fptAllOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.uctToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.uctOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.cstToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.cstOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.tmtOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.netmcToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.netmcOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umtOfP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umrtToP, StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.umrtOfP,
      StratonovichHamSecondMomentLeanAuditBridge.CameronInterface.exPrmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cxToP, StratonovichHamSecondMomentLeanAuditBridge.MaskedAuxiliaryReal.cxOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edfToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edfOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.tcToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.tcOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.admToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.admOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.neAdmToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.neAdmOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfToP', StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.wfOfP', StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.khToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.khOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnTToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnTOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.cnOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbTToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbTOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.ceaAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.crToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.crOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.rhbOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petAllToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.petAllOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.m4bToP, StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.m4bOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingDampedNorms.gdToP, StratonovichHamSecondMomentLeanAuditBridge.PairingDampedNorms.gdOfP, StratonovichHamSecondMomentLeanAuditBridge.PairingSmoothedNorms.sdToP, StratonovichHamSecondMomentLeanAuditBridge.PairingSmoothedNorms.sdOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.sswTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.sswTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.slTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.slTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.rsTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.rsTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m87TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m87TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swmTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swmTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m84TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.m84TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jdlTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jdlTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.dlhTToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.dlhTOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.he3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.he3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.te3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.te3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.cc3TToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.cc3TOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.splOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.wmbOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.swwlOfP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttToP, StratonovichHamSecondMomentLeanAuditBridge.WickInterface.jttOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.twwToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.twwOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.tmmToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.tmmOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.fol2ToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.fol2OfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.gfToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.gfOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.exl2ToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.exl2OfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.mtToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.mtOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.fmsToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.fmsOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sccToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sccOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.trvToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.trvOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.dliToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.dliOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.vdToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.vdOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sftToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sftOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.isoToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.isoOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sftgToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sftgOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.vcToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.vcOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.snToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.snOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.trToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.trOfP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.smToP, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.smOfP,
      StratonovichHamSecondMomentLeanAuditBridge.MildInterface.omToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.omOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.pmToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.pmOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.jmToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.jmOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.fcToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.fcOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.fmToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.fmOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.tfToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.tfOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.tfiToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.tfiOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.jmiToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.jmiOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.pvToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.pvOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.gwToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.gwOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.evToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.evOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mcToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.mcOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.riToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.riOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.duwToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.duwOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.durToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.durOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.rsToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.rsOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.fcrToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.fcrOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.frtToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.frtOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.frwToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.frwOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.frrToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.frrOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.lauToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.lauOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.rkToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.rkOfP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.envToP, StratonovichHamSecondMomentLeanAuditBridge.MildInterface.envOfP]))

end StratonovichHamSecondMomentLeanAuditBridge
