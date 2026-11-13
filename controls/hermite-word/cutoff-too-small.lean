import StratonovichHAMAudit.HermiteWord

namespace StratonovichHAMAudit.HermiteWordConsumer
open StratonovichHAMAudit.HermiteWord

-- Coefficients in the unnormalized probabilists' Hermite basis:
-- x He_n = He_(n+1) + n He_(n-1). This defines the finite recurrence;
-- no assertion about Gaussian L² or polynomial realization is imported.
private def vacuum (n : Nat) : Nat := if n = 0 then 1 else 0
private def insert (_ : Unit) (p : Nat → Nat) (n : Nat) : Nat :=
  (if n = 0 then 0 else p (n-1)) + (n+1) * p (n+1)
private def frame (_ : Unit) (p : Nat → Nat) := p
private def project (N : Nat) (p : Nat → Nat) (n : Nat) :=
  if n ≤ N then p n else 0
private def Good (d : Unit → Nat) (p : Nat → Nat) : Prop :=
  ∀ n, d () < n → p n = 0

private theorem vacuum_good : Good (fun _ => 0) vacuum := by
  intro n hn
  simp only [vacuum]
  split <;> omega

private theorem insert_good (d : Unit → Nat) (i : Unit) (p : Nat → Nat)
    (hp : Good d p) : Good (bump i d) (insert i p) := by
  intro n hn
  have hi : i = () := by cases i; rfl
  subst i
  simp [bump] at hn
  have h₁ : p (n-1) = 0 := hp _ (by omega)
  have h₂ : p (n+1) = 0 := hp _ (by omega)
  simp [insert, h₁, h₂]

private theorem frame_good (d : Unit → Nat) (b : Unit) (p : Nat → Nat)
    (hp : Good d p) : Good d (frame b p) := hp

private theorem project_fixes (N : Nat) (d : Unit → Nat) (p : Nat → Nat)
    (hd : ∀ c, d c ≤ N) (hp : Good d p) : project N p = p := by
  funext n
  simp only [project]
  split
  · rfl
  · exact (hp n (by have h := hd (); omega)).symm

private theorem count_length (w : List (Unit × Unit)) : counts w () = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : a.1 = () := by cases a with | mk i b => cases i; rfl
    simp [counts, bump, ha, ih]

-- Actual recurrence consumer, arbitrary word length and cutoff; not a third
-- public claim and not the analytic Hermite/Hilbert realization theorem.
example (w : List (Unit × Unit)) (N : Nat) (hN : w.length ≤ N) :
    cut (project N) insert frame vacuum w = raw insert frame vacuum w := by
  apply cut_eq_raw Good insert frame (project N) vacuum (fun _ => N)
    vacuum_good insert_good frame_good (project_fixes N) w
  intro c
  cases c
  simpa only [count_length] using hN

-- Four insertions preserve the vacuum self-contraction 3 at cutoff 4.
example : cut (project 4) insert frame vacuum [ ((),()), ((),()), ((),()), ((),()) ] 0 = 3 := by
  decide
-- An insufficient cutoff actually changes the second-order vector.
example : cut (project 1) insert frame vacuum [ ((),()), ((),()) ] 2 = 0 := by decide
example : raw insert frame vacuum [ ((),()), ((),()) ] 2 = 1 := by decide
-- Removing lowering loses the self-contraction, so creation-only is false.
example : raw insert frame vacuum [ ((),()), ((),()) ] 0 = 1 := by decide

example : cut (project 1) insert frame vacuum [((),()),((),())] 2 = raw insert frame vacuum [((),()),((),())] 2 := by decide

end StratonovichHAMAudit.HermiteWordConsumer
