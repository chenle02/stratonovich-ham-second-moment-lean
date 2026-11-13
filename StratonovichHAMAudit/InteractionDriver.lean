module
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.InteractionDriver

def temporalH (a : ℝ) : ℝ := 1-a/2
def midpoint (H theta : ℝ) : ℝ := (H+theta)/2
def mixC (u v : ℝ) : ℝ := u*v/(u+v)
def dyadicFactor (H theta p : ℝ) : ℝ :=
  (2:ℝ)^(-(H-midpoint H theta-1/p))

theorem temporal_range (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    1/2 < temporalH a ∧ temporalH a < 1 := by
  unfold temporalH
  constructor <;> linarith

theorem variance_norm (C h a L : ℝ) (hC : 0 ≤ C) (hh : 0 < h) (hL : 0 ≤ L) :
    Real.sqrt (C*h^(2-a)*L^2) = Real.sqrt C*h^(1-a/2)*L := by
  have hs : Real.sqrt (h^(2-a)) = h^(1-a/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hh.le]
    congr 1
    ring
  rw [Real.sqrt_mul (mul_nonneg hC (Real.rpow_nonneg hh.le _)),
    Real.sqrt_sq hL, Real.sqrt_mul hC, hs]

theorem gaussian_prefactor (P u v : ℝ) (hP : 0 < P) (hu : 0 < u) (hv : 0 < v) :
    (1/Real.sqrt P)*(1/Real.sqrt (u*v*(u+v)))*
      Real.sqrt (P/mixC u v) = 1/(u*v) := by
  have hc : 0 < mixC u v := by unfold mixC; positivity
  have hpr : 0 < Real.sqrt P := Real.sqrt_pos.2 hP
  have hdr : 0 < Real.sqrt (u*v*(u+v)) := Real.sqrt_pos.2 (by positivity)
  have hcr : 0 < Real.sqrt (mixC u v) := Real.sqrt_pos.2 hc
  have hs : Real.sqrt (u*v*(u+v))*Real.sqrt (mixC u v) = u*v := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ u*v*(u+v))]
    have he : u*v*(u+v)*mixC u v = (u*v)^2 := by
      unfold mixC
      field_simp [(add_pos hu hv).ne']
    rw [he, Real.sqrt_sq (by positivity)]
  rw [Real.sqrt_div hP.le]
  calc
    (1/Real.sqrt P)*(1/Real.sqrt (u*v*(u+v)))*
        (Real.sqrt P/Real.sqrt (mixC u v)) =
        1/(Real.sqrt (u*v*(u+v))*Real.sqrt (mixC u v)) := by
      field_simp [hpr.ne', hdr.ne', hcr.ne']
    _ = 1/(u*v) := by rw [hs]

theorem gaussian_exponent (u v z : ℝ) (hu : 0 < u) (hv : 0 < v) :
    z^2/(4*mixC u v) = z^2/(4*u)+z^2/(4*v) := by
  unfold mixC
  field_simp [hu.ne', hv.ne', (add_pos hu hv).ne']
  ring

theorem holder_parameters (H theta p : ℝ) (htheta : 1/2 < theta)
    (hthetaH : theta < H) (hH1 : H < 1) (hp : 0 < p)
    (hcut : 2/(H-theta) < p) :
    theta < midpoint H theta ∧ midpoint H theta < H ∧
    midpoint H theta < 1 ∧ 0 < H-midpoint H theta-1/p ∧ 2 < p := by
  have hd : 0 < H-theta := by linarith
  have hb : 2 < p*(H-theta) := (div_lt_iff₀ hd).mp hcut
  have hi : (1:ℝ)/p < (H-theta)/2 := by
    apply (div_lt_iff₀ hp).2
    nlinarith
  have hpd : p*(H-theta) < p := by
    have h := mul_pos hp (show 0 < 1-(H-theta) by linarith)
    nlinarith
  unfold midpoint
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem dyadic_ratio (H theta p : ℝ) (hmargin : 0 < H-midpoint H theta-1/p) :
    0 < dyadicFactor H theta p ∧ dyadicFactor H theta p < 1 := by
  unfold dyadicFactor
  constructor
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem box_margin (a p : ℝ) (ha : a < 1) (hp : 0 < p)
    (hcut : 4/(1-a) < p) : 0 < (1-a)/2-2/p := by
  have h : 4 < p*(1-a) := (div_lt_iff₀ (show (0:ℝ) < 1-a by linarith)).mp hcut
  have hi : (2:ℝ)/p < (1-a)/2 := by
    apply (div_lt_iff₀ hp).2
    nlinarith
  linarith

theorem box_scale (delta a p : ℝ) (hd : 0 < delta) :
    delta^((1-a)/2)*(delta^(-(2:ℝ)))^(1/p) = delta^((1-a)/2-2/p) := by
  rw [← Real.rpow_mul hd.le, ← Real.rpow_add hd]
  congr 1
  ring

end StratonovichHAMAudit.InteractionDriver
