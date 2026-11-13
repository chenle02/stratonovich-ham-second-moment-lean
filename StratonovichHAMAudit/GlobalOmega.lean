module
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.GlobalOmega

def envelopePolynomial (x : ℝ) : ℝ :=
  -237888*x^15 + 2567920*x^14 - 10605344*x^13 + 17964536*x^12 + 3700636*x^11 - 59045877*x^10 + 66291248*x^9 + 36266494*x^8 - 125535292*x^7 + 58424029*x^6 + 68792033*x^5 - 94022217*x^4 + 42981706*x^3 - 8102234*x^2 + 516600*x + 9900

def envelopeDenom (x : ℝ) : ℝ :=
  750*(3-x)*(2-x)*(1-x)*(5-2*x)*(3-2*x)*(5-3*x)*(3-4*x-2*x^2)

def envelopeRational (x : ℝ) : ℝ :=
  2*(1-x^2+x^4/2)*(1-4*x^2)/(1-3*x/5)*
    (1/(2*(1-x))+x*(1-x)/(2-x)+x*(x+1)*(1-x)^2/(3*(3-x))-
      2*(1-3*x/5)*(1/(3-2*x)+(2*x+1)*(1-x)/(3*(5-2*x)))*
        x*(177/100)*(1-7*x/5))*(3-4*x)/(3-4*x-2*x^2)

theorem left_certificate (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ (4:ℝ)^15*envelopePolynomial (t/4) := by
  have h1 : 0 ≤ 1-t := by linarith
  have hid : (4:ℝ)^15*envelopePolynomial (t/4)-1 =
    (10630044057599:ℝ)*t^0*(1-t)^15 +
    (298124417433585:ℝ)*t^1*(1-t)^14 +
    (2513855498420119:ℝ)*t^2*(1-t)^13 +
    (11108582904823353:ℝ)*t^3*(1-t)^12 +
    (30835186027461291:ℝ)*t^4*(1-t)^11 +
    (58554861260633157:ℝ)*t^5*(1-t)^10 +
    (79751967489125491:ℝ)*t^6*(1-t)^9 +
    (80316614660581085:ℝ)*t^7*(1-t)^8 +
    (61414936532707037:ℝ)*t^8*(1-t)^7 +
    (36921141989698675:ℝ)*t^9*(1-t)^6 +
    (18353430194004037:ℝ)*t^10*(1-t)^5 +
    (7893814205477547:ℝ)*t^11*(1-t)^4 +
    (2890010244293689:ℝ)*t^12*(1-t)^3 +
    (811168303884183:ℝ)*t^13*(1-t)^2 +
    (146648694693297:ℝ)*t^14*(1-t)^1 +
    (12356981993087:ℝ)*t^15*(1-t)^0 := by
    unfold envelopePolynomial
    ring
  have hn : 0 ≤
    (10630044057599:ℝ)*t^0*(1-t)^15 +
    (298124417433585:ℝ)*t^1*(1-t)^14 +
    (2513855498420119:ℝ)*t^2*(1-t)^13 +
    (11108582904823353:ℝ)*t^3*(1-t)^12 +
    (30835186027461291:ℝ)*t^4*(1-t)^11 +
    (58554861260633157:ℝ)*t^5*(1-t)^10 +
    (79751967489125491:ℝ)*t^6*(1-t)^9 +
    (80316614660581085:ℝ)*t^7*(1-t)^8 +
    (61414936532707037:ℝ)*t^8*(1-t)^7 +
    (36921141989698675:ℝ)*t^9*(1-t)^6 +
    (18353430194004037:ℝ)*t^10*(1-t)^5 +
    (7893814205477547:ℝ)*t^11*(1-t)^4 +
    (2890010244293689:ℝ)*t^12*(1-t)^3 +
    (811168303884183:ℝ)*t^13*(1-t)^2 +
    (146648694693297:ℝ)*t^14*(1-t)^1 +
    (12356981993087:ℝ)*t^15*(1-t)^0 := by positivity
  linarith

theorem right_certificate (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ (4:ℝ)^15*envelopePolynomial ((1+t)/4) := by
  have h1 : 0 ≤ 1-t := by linarith
  have hid : (4:ℝ)^15*envelopePolynomial ((1+t)/4)-1 =
    (12356981993087:ℝ)*t^0*(1-t)^15 +
    (224060765099313:ℝ)*t^1*(1-t)^14 +
    (1894937289568407:ℝ)*t^2*(1-t)^13 +
    (9799655243171641:ℝ)*t^3*(1-t)^12 +
    (34453566936433323:ℝ)*t^4*(1-t)^11 +
    (87031904519822405:ℝ)*t^5*(1-t)^10 +
    (163125524987087987:ℝ)*t^6*(1-t)^9 +
    (231150225523443421:ℝ)*t^7*(1-t)^8 +
    (249909141873911517:ℝ)*t^8*(1-t)^7 +
    (206372784329731187:ℝ)*t^9*(1-t)^6 +
    (129237504527758405:ℝ)*t^10*(1-t)^5 +
    (60326501022497451:ℝ)*t^11*(1-t)^4 +
    (20332988225551929:ℝ)*t^12*(1-t)^3 +
    (4674097187389335:ℝ)*t^13*(1-t)^2 +
    (655486353407985:ℝ)*t^14*(1-t)^1 +
    (42278584319999:ℝ)*t^15*(1-t)^0 := by
    unfold envelopePolynomial
    ring
  have hn : 0 ≤
    (12356981993087:ℝ)*t^0*(1-t)^15 +
    (224060765099313:ℝ)*t^1*(1-t)^14 +
    (1894937289568407:ℝ)*t^2*(1-t)^13 +
    (9799655243171641:ℝ)*t^3*(1-t)^12 +
    (34453566936433323:ℝ)*t^4*(1-t)^11 +
    (87031904519822405:ℝ)*t^5*(1-t)^10 +
    (163125524987087987:ℝ)*t^6*(1-t)^9 +
    (231150225523443421:ℝ)*t^7*(1-t)^8 +
    (249909141873911517:ℝ)*t^8*(1-t)^7 +
    (206372784329731187:ℝ)*t^9*(1-t)^6 +
    (129237504527758405:ℝ)*t^10*(1-t)^5 +
    (60326501022497451:ℝ)*t^11*(1-t)^4 +
    (20332988225551929:ℝ)*t^12*(1-t)^3 +
    (4674097187389335:ℝ)*t^13*(1-t)^2 +
    (655486353407985:ℝ)*t^14*(1-t)^1 +
    (42278584319999:ℝ)*t^15*(1-t)^0 := by positivity
  linarith

theorem polynomial_pos (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    0 < envelopePolynomial x := by
  by_cases h : x ≤ 1/4
  · have hb := left_certificate (4*x) (by linarith) (by linarith)
    have he : (4*x)/4=x := by ring
    rw [he] at hb
    nlinarith
  · have hb := right_certificate (4*x-1) (by linarith) (by linarith)
    have he : (1+(4*x-1))/4=x := by ring
    rw [he] at hb
    nlinarith

theorem rational_lt_one (x : ℝ) (hx : 0 < x) (hh : x ≤ 1/2) :
    envelopeRational x < 1 := by
  have h1 : 0 < 1-x := by linarith
  have h2 : 0 < 2-x := by linarith
  have h3 : 0 < 3-x := by linarith
  have h4 : 0 < 3-2*x := by linarith
  have h5 : 0 < 5-2*x := by linarith
  have h6 : 0 < 5-3*x := by linarith
  have hg : 0 < 1-3*x/5 := by linarith
  have h8 : 0 < 3-4*x-2*x^2 := by
    have hm := mul_nonneg hx.le (sub_nonneg.mpr hh)
    nlinarith
  have hd : 0 < envelopeDenom x := by
    unfold envelopeDenom
    positivity
  have n4 : 3-x*2 ≠ 0 := by simpa only [mul_comm] using ne_of_gt h4
  have n5 : 5-x*2 ≠ 0 := by simpa only [mul_comm] using ne_of_gt h5
  have n8 : 3-x*4-x^2*2 ≠ 0 := by simpa only [mul_comm] using ne_of_gt h8
  have hid : envelopeDenom x*(1-envelopeRational x)=x*envelopePolynomial x := by
    unfold envelopeDenom envelopeRational envelopePolynomial
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3, ne_of_gt h4,
      ne_of_gt h5, ne_of_gt h6, ne_of_gt hg, ne_of_gt h8, n4, n5, n8]
    ring
  have hp := mul_pos hx (polynomial_pos x hx.le hh)
  by_contra hnot
  have hv : 1 ≤ envelopeRational x := le_of_not_gt hnot
  have hn := mul_nonpos_of_nonneg_of_nonpos hd.le (sub_nonpos.mpr hv)
  rw [hid] at hn
  linarith

end StratonovichHAMAudit.GlobalOmega
