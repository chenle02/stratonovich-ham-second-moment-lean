module
public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
namespace StratonovichHAMAudit.MiddleCross

def actual (b c : ℝ) : ℝ :=
  (2*b^2+4*b*c+2*c^2-c+1) /
    (8*b*c*(b+1)*(2*b+1)*(b+c-1)*(2*b+2*c-1))
def massK (b c : ℝ) : ℝ := 1/(4*b*c*(c+1))
def resolvent (b c r : ℝ) : ℝ :=
  (b+c+r+1)/(4*b*c*(c+1)*r*(b+c+r)*(b+r+1))
def part1 (b d e : ℝ) : ℝ :=
  (d+e+b+1)/(d*e*(b+d+1)*(b+e+1))
def part2 (b c d e : ℝ) : ℝ :=
  (d^2+d*e+e^2+(2*b+c+1)*(d+e)+(b+c)*(b+1)) /
    (d*e*(b+c+d)*(b+c+e)*(b+d+1)*(b+e+1))
def upper (b c d e : ℝ) : ℝ :=
  resolvent b c e + massK b c*(part1 b d e+part2 b c d e)/(d+e)
def denominator (b c d e : ℝ) : ℝ :=
  8*b*c*d*e*(b+1)*(2*b+1)*(c+1)*(d+e)*(b+c-1)*
    (b+c+d)*(b+c+e)*(b+d+1)*(b+e+1)*(2*b+2*c-1)
def numerator (b c d e : ℝ) : ℝ :=
  (2*b^2+4*b*c+2*c^2-c+1)*d*e*(c+1)*(d+e)*
    (b+c+d)*(b+c+e)*(b+d+1)*(b+e+1) -
  2*(b+1)*(2*b+1)*(b+c-1)*(2*b+2*c-1)*
    (d*(d+e)*(b+c+d)*(b+d+1)*(b+c+e+1) +
      (b+c+d)*(b+c+e)*(b+d+e+1) +
      (d^2+d*e+e^2+(2*b+c+1)*(d+e)+(b+c)*(b+1)))
def paramB (z : ℝ) : ℝ := (z^2-1)/(2*z)
def paramE (z : ℝ) : ℝ := (z^2+1)/(2*z)
def paramC (z t : ℝ) : ℝ := ((paramB z+1)*t-(paramB z-1)/t)/2

def paramD (z t : ℝ) : ℝ := ((paramB z+1)*t+(paramB z-1)/t)/2
def certificate (x y : ℝ) : ℝ := y * (
    (((((((((((((((((((((((((((((((((1*y + 28)*y + 354)*y + 2684)*y + 13660)*y + 49456)*y + 131576)*y + 261680)*y + 391296)*y + 437824)*y + 360448)*y + 211200)*y + 82944)*y + 19456)*y + 2048)*x +
    ((((((((((((((55*y + 1512)*y + 18784)*y + 140048)*y + 701336)*y + 2499784)*y + 6550296)*y + 12836128)*y + 18921216)*y + 20883712)*y + 16977536)*y + 9840128)*y + 3832832)*y + 894976)*y + 94208))*x +
    ((((((((((((((1417*y + 38240)*y + 466708)*y + 3420740)*y + 16850280)*y + 59105968)*y + 152480312)*y + 294286272)*y + 427406592)*y + 465044672)*y + 373023616)*y + 213625088)*y + 82394624)*y + 19107840)*y + 2004992))*x +
    ((((((((((((((22727*y + 601996)*y + 7216502)*y + 51985016)*y + 251810540)*y + 868957096)*y + 2206157400)*y + 4191612016)*y + 5994832256)*y + 6425997824)*y + 5081501440)*y + 2872175872)*y + 1095265792)*y + 251738112)*y + 26259456))*x +
    ((((((((((((((254372*y + 6612880)*y + 77851036)*y + 551065316)*y + 2624208512)*y + 8906236696)*y + 22245133008)*y + 41589271840)*y + 58542163584)*y + 61779578240)*y + 48119430272)*y + 26812359936)*y + 10093317120)*y + 2294575104)*y + 237334528))*x +
    ((((((((((((((2110780*y + 53855280)*y + 622592788)*y + 4329796972)*y + 20266599344)*y + 67631178328)*y + 166135404880)*y + 305522152480)*y + 423055944576)*y + 439223476096)*y + 336652184448)*y + 184694641408)*y + 68523174400)*y + 15375787008)*y + 1572855808))*x +
    ((((((((((((((13466068*y + 337223936)*y + 3828171644)*y + 26154845564)*y + 120320374608)*y + 394741504856)*y + 953482998160)*y + 1724232000224)*y + 2347593059776)*y + 2396275198080)*y + 1805705641344)*y + 974129734144)*y + 355575074816)*y + 78575386624)*y + 7927072768))*x +
    ((((((((((((((67589612*y + 1661570624)*y + 18523608516)*y + 124336959444)*y + 562165939360)*y + 1813157890264)*y + 4306136458192)*y + 7655958898336)*y + 10246137617600)*y + 10276941230464)*y + 7607029260928)*y + 4030198677504)*y + 1444733525504)*y + 313647800320)*y + 31109001216))*x +
    ((((((((((((((270870398*y + 6538490728)*y + 71598456224)*y + 472239475756)*y + 2098783816600)*y + 6655722050552)*y + 15543381818112)*y + 27170816846400)*y + 35740140455424)*y + 35213950681984)*y + 25587526626176)*y + 13298388480256)*y + 4673623743488)*y + 994293045248)*y + 96623300608))*x +
    ((((((((((((((874459282*y + 20734832000)*y + 223093795876)*y + 1446315012956)*y + 6320424114656)*y + 19714053281128)*y + 45287230089280)*y + 77861330975392)*y + 100688410891776)*y + 97461485555712)*y + 69506069344128)*y + 35413222757632)*y + 12185165672960)*y + 2534613507072)*y + 240487604224))*x +
    ((((((((((((((2283811966*y + 53221790528)*y + 562911296372)*y + 3588686613556)*y + 15428306862240)*y + 47358829585016)*y + 107086380369088)*y + 181209897521568)*y + 230552554699328)*y + 219395649011328)*y + 153651054921600)*y + 76761971877376)*y + 25850098629632)*y + 5250420224000)*y + 485086054400))*x +
    ((((((((((((((4826029538*y + 110603022648)*y + 1150662129008)*y + 7218434488372)*y + 30552070847320)*y + 92373485329128)*y + 205804912147392)*y + 343184440420416)*y + 430182179905600)*y + 403085090851584)*y + 277684936993664)*y + 136256033695744)*y + 44972739813888)*y + 8927197915136)*y + 802957824000))*x +
    ((((((((((((((8218851284*y + 185383193104)*y + 1898507504164)*y + 11729095321804)*y + 48920555288032)*y + 145855525618056)*y + 320644070286512)*y + 527815115807840)*y + 653253048136320)*y + 604300123774336)*y + 410791095094144)*y + 198708431823616)*y + 64552357450752)*y + 12581167542272)*y + 1106990444544))*x +
    ((((((((((((((11183782540*y + 248493175504)*y + 2507313321276)*y + 15270399802372)*y + 62837415675856)*y + 185014573044104)*y + 402062604887600)*y + 654862449522912)*y + 802621407060352)*y + 735766784662400)*y + 495884624297088)*y + 237879461960960)*y + 76630862958080)*y + 14802571648000)*y + 1289321848832))*x +
    ((((((((((((((11984649124*y + 262569628160)*y + 2612972571412)*y + 15706031299412)*y + 63852219358768)*y + 185981808058312)*y + 400409544657904)*y + 647134292910112)*y + 788337113564736)*y + 719544094696576)*y + 483747050599040)*y + 231944520802816)*y + 74848983220224)*y + 14520748802048)*y + 1274197587968))*x +
    ((((((((((((((9885272348*y + 213777126304)*y + 2100556974908)*y + 12477032327676)*y + 50192120075712)*y + 144905056192392)*y + 309848250179248)*y + 498508265259744)*y + 606106158408512)*y + 553753146532736)*y + 373877356875136)*y + 180713736328192)*y + 59050415532544)*y + 11662726320128)*y + 1048996761600))*x +
    ((((((((((((((6052923401*y + 129352117468)*y + 1256452921150)*y + 7385206406312)*y + 29445863593132)*y + 84437195815480)*y + 179798846509960)*y + 288944179278352)*y + 352126943711360)*y + 323726375768896)*y + 220911778516096)*y + 108459689971200)*y + 36202359308288)*y + 7351264885760)*y + 684966758400))*x +
    ((((((((((((((2590042735*y + 54757609368)*y + 526440369196)*y + 3066335922468)*y + 12138468731144)*y + 34646712967664)*y + 73665081916712)*y + 118637765082944)*y + 145491395759616)*y + 135213713734656)*y + 93733029452288)*y + 46991615202560)*y + 16103027874304)*y + 3375705144320)*y + 326571520000))*x +
    ((((((((((((((690952577*y + 14468003424)*y + 137841467624)*y + 796745823160)*y + 3136787863160)*y + 8930460873656)*y + 19006962914184)*y + 30767520242592)*y + 38095203501248)*y + 35912615870400)*y + 25371025696000)*y + 13020278353152)*y + 4585999234560)*y + 991683084288)*y + 99260620800))*x +
    ((((((((((((((86472015*y + 1795323740)*y + 16970868250)*y + 97478919300)*y + 382298120540)*y + 1087721023760)*y + 2322535698280)*y + 3788061992400)*y + 4746895648320)*y + 4548594982400)*y + 3279014122880)*y + 1722640193280)*y + 622624204800)*y + 138380636160)*y + 14247936000)))

theorem certificate_pos (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    0 < certificate x y := by
  unfold certificate
  positivity

set_option maxHeartbeats 2000000 in
 theorem parameter_identity (z t : ℝ) (hz : 0 < z) (ht : 0 < t) :
    numerator (paramB z) (paramC z t) (paramD z t) (paramE z) *
      (32768*t^7*z^9) = certificate (z-2) (t-1) := by
  unfold numerator paramC paramD paramE paramB certificate
  field_simp [hz.ne', ht.ne']
  ring

 theorem parameter_numerator_pos (z t : ℝ) (hz : 2 ≤ z) (ht : 1 < t) :
    0 < numerator (paramB z) (paramC z t) (paramD z t) (paramE z) := by
  have hzpos : 0 < z := by linarith
  have htpos : 0 < t := by linarith
  have hs : 0 < (32768:ℝ)*t^7*z^9 := by positivity
  have hp : 0 < numerator (paramB z) (paramC z t) (paramD z t) (paramE z) *
      (32768*t^7*z^9) := by
    rw [parameter_identity z t hzpos htpos]
    exact certificate_pos (z-2) (t-1) (by linarith) (by linarith)
  exact (mul_pos_iff_of_pos_right hs).1 hp

set_option maxHeartbeats 2000000 in
 theorem difference_identity (b c d e : ℝ) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 0 < d) (he : 0 < e) :
    actual b c - upper b c d e = numerator b c d e / denominator b c d e := by
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hbc : 0 < b+c-1 := by linarith
  have h2bc : 0 < 2*b+2*c-1 := by linarith
  have hbe : 0 < b+c+e := by positivity
  have hbd : 0 < b+c+d := by positivity
  have hb1d : 0 < b+d+1 := by positivity
  have hb1e : 0 < b+e+1 := by positivity
  have hb1 : 0 < b+1 := by positivity
  have h2b1 : 0 < 2*b+1 := by positivity
  have hc1 : 0 < c+1 := by positivity
  have hde : 0 < d+e := by positivity
  unfold actual upper resolvent massK part1 part2 numerator denominator
  field_simp (disch := first | positivity | linarith)
  ring

set_option maxHeartbeats 2000000 in
 theorem resolvent_difference (b c d e : ℝ) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 0 < d) (he : 0 < e) :
    resolvent b c d - resolvent b c e =
      (e-d)*massK b c*(part1 b d e+part2 b c d e) := by
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hbe : 0 < b+c+e := by positivity
  have hbd : 0 < b+c+d := by positivity
  have hb1d : 0 < b+d+1 := by positivity
  have hb1e : 0 < b+e+1 := by positivity
  have hc1 : 0 < c+1 := by positivity
  unfold resolvent massK part1 part2
  field_simp (disch := first | positivity | linarith)
  ring

 theorem root_numerator_pos (b c : ℝ) (hb : 1 ≤ b) (hc : 1 < c) :
    0 < numerator b c (Real.sqrt (b^2+c^2-1)) (Real.sqrt (b^2+1)) := by
  let d := Real.sqrt (b^2+c^2-1)
  let e := Real.sqrt (b^2+1)
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hcsq : 1 < c^2 := by nlinarith [sq_nonneg (c-1)]
  have hrad : 0 < b^2+c^2-1 := by nlinarith [sq_nonneg b]
  have hd0 : 0 < d := Real.sqrt_pos.2 hrad
  have he0 : 0 < e := Real.sqrt_pos.2 (by positivity)
  have hdsq : d^2 = b^2+c^2-1 := Real.sq_sqrt hrad.le
  have hesq : e^2 = b^2+1 := Real.sq_sqrt (by positivity)
  have hegt : b < e := (sq_lt_sq₀ hb0.le he0.le).1 (by nlinarith)
  have hdge : b ≤ d := (sq_le_sq₀ hb0.le hd0.le).1 (by nlinarith)
  let z := b+e
  let t := (d+c)/(b+1)
  have hz : 2 ≤ z := by dsimp [z]; linarith
  have hz0 : 0 < z := by linarith
  have hb1 : 0 < b+1 := by positivity
  have ht : 1 < t := by
    dsimp [t]
    exact (one_lt_div hb1).2 (by linarith)
  have ht0 : 0 < t := by linarith
  have hB : paramB z = b := by
    unfold paramB
    field_simp [hz0.ne']
    dsimp [z]
    nlinarith [hesq]
  have hE : paramE z = e := by
    unfold paramE
    field_simp [hz0.ne']
    dsimp [z]
    nlinarith [hesq]
  have hmul : (b+1)*t = d+c := by
    dsimp [t]
    field_simp [hb1.ne']
  have hsubmul : (d-c)*t = b-1 := by
    dsimp [t]
    field_simp [hb1.ne']
    nlinarith [hdsq]
  have hdiv : (b-1)/t = d-c := (div_eq_iff ht0.ne').2 hsubmul.symm
  have hC : paramC z t = c := by
    unfold paramC
    rw [hB,hmul,hdiv]
    ring
  have hD : paramD z t = d := by
    unfold paramD
    rw [hB,hmul,hdiv]
    ring
  have hp := parameter_numerator_pos z t hz ht
  rw [hB,hC,hD,hE] at hp
  exact hp

 theorem middle_bound (b c : ℝ) (hb : 1 ≤ b) (hc : 1 < c) :
    upper b c (Real.sqrt (b^2+c^2-1)) (Real.sqrt (b^2+1)) < actual b c := by
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hcsq : 1 < c^2 := by nlinarith [sq_nonneg (c-1)]
  have hd : 0 < Real.sqrt (b^2+c^2-1) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg b])
  have he : 0 < Real.sqrt (b^2+1) := Real.sqrt_pos.2 (by positivity)
  have hbc : 0 < b+c-1 := by linarith
  have h2bc : 0 < 2*b+2*c-1 := by linarith
  have hden : 0 < denominator b c (Real.sqrt (b^2+c^2-1)) (Real.sqrt (b^2+1)) := by
    unfold denominator
    positivity
  have hp := root_numerator_pos b c hb hc
  have hdiff : 0 < actual b c - upper b c (Real.sqrt (b^2+c^2-1)) (Real.sqrt (b^2+1)) := by
    rw [difference_identity b c _ _ hb hc.le hd he]
    exact div_pos hp hden
  linarith

end StratonovichHAMAudit.MiddleCross
end
