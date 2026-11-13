import Std.Tactic

namespace StratonovichHAMAudit.HermiteWord

variable {C B V : Type} [DecidableEq C]

def bump (i : C) (d : C → Nat) : C → Nat :=
  fun c => d c + if c = i then 1 else 0

def counts : List (C × B) → C → Nat
  | [] => fun _ => 0
  | (i, _) :: w => bump i (counts w)

def raw (J : C → V → V) (F : B → V → V) (v₀ : V) : List (C × B) → V
  | [] => v₀
  | (i, b) :: w => F b (J i (raw J F v₀ w))

def cut (P : V → V) (J : C → V → V) (F : B → V → V)
    (v₀ : V) : List (C × B) → V
  | [] => v₀
  | (i, b) :: w => F b (P (J i (P (cut P J F v₀ w))))

theorem raw_support
    (Good : (C → Nat) → V → Prop)
    (J : C → V → V) (F : B → V → V) (v₀ : V)
    (hv₀ : Good (fun _ => 0) v₀)
    (hJ : ∀ d i v, Good d v → Good (bump i d) (J i v))
    (hF : ∀ d b v, Good d v → Good d (F b v))
    (w : List (C × B)) : Good (counts w) (raw J F v₀ w) := by
  induction w with
  | nil => exact hv₀
  | cons a w ih =>
    exact hF _ a.2 _ (hJ _ a.1 _ ih)

theorem cut_eq_raw
    (Good : (C → Nat) → V → Prop)
    (J : C → V → V) (F : B → V → V) (P : V → V)
    (v₀ : V) (N : C → Nat)
    (hv₀ : Good (fun _ => 0) v₀)
    (hJ : ∀ d i v, Good d v → Good (bump i d) (J i v))
    (hF : ∀ d b v, Good d v → Good d (F b v))
    (hP : ∀ d v, (∀ c, d c ≤ N c) → Good d v → P v = v)
    (w : List (C × B)) (hN : ∀ c, counts w c ≤ N c) :
    cut P J F v₀ w = raw J F v₀ w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hs : ∀ c, counts w c ≤ N c := by
      intro c
      have hc := hN c
      simp only [counts, bump] at hc
      omega
    have hw := raw_support Good J F v₀ hv₀ hJ hF w
    have hp₀ := hP (counts w) (raw J F v₀ w) hs hw
    have hp₁ := hP (bump a.1 (counts w)) (J a.1 (raw J F v₀ w))
      hN (hJ _ _ _ hw)
    change F a.2 (P (J a.1 (P (cut P J F v₀ w)))) =
      F a.2 (J a.1 (raw J F v₀ w))
    rw [ih hs, hp₀, hp₁]

end StratonovichHAMAudit.HermiteWord
