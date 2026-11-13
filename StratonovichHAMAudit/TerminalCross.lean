module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

set_option autoImplicit false

namespace StratonovichHAMAudit.TerminalCross

def numP (c : ℝ) : ℝ := c ^ 2 + c + 1
def numN (b c : ℝ) : ℝ := b * numP c + c ^ 3 + c + 1

def polynomial (b c : ℝ) : ℝ :=
  (c + 1) ^ 2 * ((c ^ 2 + 1) * b ^ 2 + c ^ 2 - 1) * numN b c ^ 2 -
    4 * (c ^ 2 + 1) * numP c ^ 2 * (b + c - 1) ^ 2 * (b + 1) ^ 2

def certificate (x y : ℝ) : ℝ := y * (
  x ^ 4 * (y ^ 7 + 12*y ^ 6 + 61*y ^ 5 + 176*y ^ 4 + 315*y ^ 3 +
    354*y ^ 2 + 234*y + 72) +
  x ^ 3 * (2*y ^ 8 + 28*y ^ 7 + 172*y ^ 6 + 612*y ^ 5 + 1394*y ^ 4 +
    2098*y ^ 3 + 2056*y ^ 2 + 1212*y + 336) +
  x ^ 2 * (y ^ 9 + 18*y ^ 8 + 142*y ^ 7 + 640*y ^ 6 + 1841*y ^ 5 +
    3546*y ^ 4 + 4618*y ^ 3 + 3952*y ^ 2 + 2030*y + 480) +
  x * (2*y ^ 9 + 32*y ^ 8 + 220*y ^ 7 + 868*y ^ 6 + 2194*y ^ 5 +
    3712*y ^ 4 + 4224*y ^ 3 + 3116*y ^ 2 + 1336*y + 240) +
  (2*y ^ 9 + 28*y ^ 8 + 166*y ^ 7 + 568*y ^ 6 + 1254*y ^ 5 +
    1868*y ^ 4 + 1890*y ^ 3 + 1264*y ^ 2 + 512*y + 96))

theorem polynomial_identity (b c : ℝ) :
    polynomial b c = certificate (b - 1) (c - 1) := by
  unfold polynomial certificate numN numP
  ring

theorem polynomial_pos (b c : ℝ) (hb : 1 ≤ b) (hc : 1 < c) :
    0 < polynomial b c := by
  rw [polynomial_identity]
  have hx : 0 ≤ b - 1 := by linarith
  have hy : 0 < c - 1 := by linarith
  unfold certificate
  positivity

theorem rate_le (A s : ℝ) (hA : 0 < A) (hs : (1 : ℝ)/2 ≤ s) :
    A / (2 * (A + 1)) ≤ s * A / (A + 2 * s) := by
  have hD : 0 < A + 2*s := by linarith
  apply (div_le_div_iff₀ (by positivity) hD).2
  have h : 0 ≤ A ^ 2 * (2*s - 1) := mul_nonneg (sq_nonneg A) (by linarith)
  nlinarith

theorem exponential_difference (C D r R k w : ℝ) (hD : 0 ≤ D) (hCD : D < C)
    (hmix : (C - D) * k = C * r - D * R) :
    C * Real.exp (-r*w) - D * Real.exp (-R*w) ≤
      (C - D) * Real.exp (-k*w) := by
  have hC : 0 < C := by linarith
  have ha : 0 ≤ (C-D)/C := div_nonneg (by linarith) hC.le
  have hb : 0 ≤ D/C := div_nonneg hD hC.le
  have hab : (C-D)/C + D/C = 1 := by field_simp [hC.ne']; ring
  have hcombo : (C-D)/C * (-k*w) + D/C * (-R*w) = -r*w := by
    field_simp [hC.ne']
    linear_combination -w * hmix
  have hconv := convexOn_exp.2 (Set.mem_univ (-k*w)) (Set.mem_univ (-R*w)) ha hb hab
  simp only [smul_eq_mul, hcombo] at hconv
  have hscaled := mul_le_mul_of_nonneg_left hconv hC.le
  have hnorm : C * ((C-D)/C * Real.exp (-k*w) + D/C * Real.exp (-R*w)) =
      (C-D)*Real.exp (-k*w) + D*Real.exp (-R*w) := by
    field_simp [hC.ne']
  rw [hnorm] at hscaled
  linarith

theorem terminal_bound (b c : ℝ) (hb : 1 ≤ b) (hc : 1 < c) :
    numP c / (16*c ^ 3*(c+1)*Real.sqrt (b ^ 2+(c ^ 2-1)/(c ^ 2+1))) <
      numN b c / (32*c ^ 3*(b+c-1)*(b+1)) := by
  have hbpos : 0 < b := by linarith
  have hcpos : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 + 1 := by positivity
  have hnum : 0 ≤ c ^ 2 - 1 := by nlinarith
  let rad : ℝ := b ^ 2 + (c ^ 2 - 1)/(c ^ 2 + 1)
  have hrad : 0 < rad := by
    dsimp [rad]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hbpos) (div_nonneg hnum hc2.le)
  have hsqrt : 0 < Real.sqrt rad := Real.sqrt_pos.2 hrad
  let U : ℝ := 2 * numP c * (b+c-1) * (b+1)
  let V : ℝ := (c+1) * numN b c
  have hbc : 0 < b+c-1 := by linarith
  have hU : 0 < U := by dsimp [U, numP]; positivity
  have hV : 0 < V := by dsimp [V, numN, numP]; positivity
  have hradid : (c ^ 2+1)*rad = (c ^ 2+1)*b ^ 2+c ^ 2-1 := by
    dsimp [rad]
    field_simp [hc2.ne']
    ring
  have hid : (c ^ 2+1)*((V*Real.sqrt rad) ^ 2-U ^ 2) = polynomial b c := by
    calc
      _ = V ^ 2*((c ^ 2+1)*rad)-(c ^ 2+1)*U ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hrad.le]
        ring
      _ = polynomial b c := by
        rw [hradid]
        dsimp [V, U, polynomial]
        ring
  have hprod : 0 < (c ^ 2+1)*((V*Real.sqrt rad) ^ 2-U ^ 2) := by
    rw [hid]
    exact polynomial_pos b c hb hc
  have hinner : 0 < (V*Real.sqrt rad) ^ 2-U ^ 2 :=
    (mul_pos_iff_of_pos_left hc2).1 hprod
  have hsq : U ^ 2 < (V*Real.sqrt rad) ^ 2 := by linarith
  have huv : U < V*Real.sqrt rad :=
    (sq_lt_sq₀ hU.le (mul_pos hV hsqrt).le).1 hsq
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  have hclear := mul_lt_mul_of_pos_left huv (show 0 < 16*c ^ 3 by positivity)
  convert hclear using 1 <;> dsimp [U, V, rad] <;> ring

end StratonovichHAMAudit.TerminalCross
