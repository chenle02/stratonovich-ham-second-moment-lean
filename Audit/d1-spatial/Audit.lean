module

import StratonovichHAMSecondMoment.D1Spatial

set_option autoImplicit false
set_option pp.all true

#check @StratonovichHAMSecondMoment.D1Spatial.closers
#print axioms StratonovichHAMSecondMoment.D1Spatial.closers
#check @StratonovichHAMSecondMoment.D1Spatial.spatialPair
#print axioms StratonovichHAMSecondMoment.D1Spatial.spatialPair
#check @StratonovichHAMSecondMoment.D1Spatial.spatialPair_const
#print axioms StratonovichHAMSecondMoment.D1Spatial.spatialPair_const
#check @StratonovichHAMSecondMoment.D1Spatial.Ksp
#print axioms StratonovichHAMSecondMoment.D1Spatial.Ksp
#check @StratonovichHAMSecondMoment.D1Spatial.pairing_inv
#print axioms StratonovichHAMSecondMoment.D1Spatial.pairing_inv
#check @StratonovichHAMSecondMoment.D1Spatial.filter_not_closing
#print axioms StratonovichHAMSecondMoment.D1Spatial.filter_not_closing
#check @StratonovichHAMSecondMoment.D1Spatial.card_closers
#print axioms StratonovichHAMSecondMoment.D1Spatial.card_closers
#check @StratonovichHAMSecondMoment.D1Spatial.pos_update_of_lt
#print axioms StratonovichHAMSecondMoment.D1Spatial.pos_update_of_lt
#check @StratonovichHAMSecondMoment.D1Spatial.pos_update_self
#print axioms StratonovichHAMSecondMoment.D1Spatial.pos_update_self
#check @StratonovichHAMSecondMoment.D1Spatial.spatialPair_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.spatialPair_le
#check @StratonovichHAMSecondMoment.D1Spatial.levelset_shift_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.levelset_shift_le
#check @StratonovichHAMSecondMoment.D1Spatial.lintegral_shift_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.lintegral_shift_le
#check @StratonovichHAMSecondMoment.D1Spatial.lintegral_centered_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.lintegral_centered_le
#check @StratonovichHAMSecondMoment.D1Spatial.riesz_conv_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.riesz_conv_le
#check @StratonovichHAMSecondMoment.D1Spatial.heatDens_eq_heatK
#print axioms StratonovichHAMSecondMoment.D1Spatial.heatDens_eq_heatK
#check @StratonovichHAMSecondMoment.D1Spatial.covEps_withDensity
#print axioms StratonovichHAMSecondMoment.D1Spatial.covEps_withDensity
#check @StratonovichHAMSecondMoment.D1Spatial.covEps_whiteCov
#print axioms StratonovichHAMSecondMoment.D1Spatial.covEps_whiteCov
#check @StratonovichHAMSecondMoment.D1Spatial.heatDens_neg
#print axioms StratonovichHAMSecondMoment.D1Spatial.heatDens_neg
#check @StratonovichHAMSecondMoment.D1Spatial.covEps_riesz_neg
#print axioms StratonovichHAMSecondMoment.D1Spatial.covEps_riesz_neg
#check @StratonovichHAMSecondMoment.D1Spatial.covEps_white_neg
#print axioms StratonovichHAMSecondMoment.D1Spatial.covEps_white_neg
#check @StratonovichHAMSecondMoment.D1Spatial.smoothCov_conv_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.smoothCov_conv_le
#check @StratonovichHAMSecondMoment.D1Spatial.riesz_eps_conv_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.riesz_eps_conv_le
#check @StratonovichHAMSecondMoment.D1Spatial.white_eps_conv_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.white_eps_conv_le
#check @StratonovichHAMSecondMoment.D1Spatial.measurable_covEps_riesz
#print axioms StratonovichHAMSecondMoment.D1Spatial.measurable_covEps_riesz
#check @StratonovichHAMSecondMoment.D1Spatial.measurable_covEps_white
#print axioms StratonovichHAMSecondMoment.D1Spatial.measurable_covEps_white
#check @StratonovichHAMSecondMoment.D1Spatial.d1_spatial_riesz
#print axioms StratonovichHAMSecondMoment.D1Spatial.d1_spatial_riesz
#check @StratonovichHAMSecondMoment.D1Spatial.d1_spatial_white
#print axioms StratonovichHAMSecondMoment.D1Spatial.d1_spatial_white
#check @StratonovichHAMSecondMoment.D1Spatial.amgm_riesz
#print axioms StratonovichHAMSecondMoment.D1Spatial.amgm_riesz
#check @StratonovichHAMSecondMoment.D1Spatial.riesz_constant_eq
#print axioms StratonovichHAMSecondMoment.D1Spatial.riesz_constant_eq
#check @StratonovichHAMSecondMoment.D1Spatial.d1_spatial_riesz_max
#print axioms StratonovichHAMSecondMoment.D1Spatial.d1_spatial_riesz_max
#check @StratonovichHAMSecondMoment.D1Spatial.amgm_white
#print axioms StratonovichHAMSecondMoment.D1Spatial.amgm_white
#check @StratonovichHAMSecondMoment.D1Spatial.d1_spatial_white_max
#print axioms StratonovichHAMSecondMoment.D1Spatial.d1_spatial_white_max
#check @StratonovichHAMSecondMoment.D1Spatial.spatial_riesz_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.spatial_riesz_le
#check @StratonovichHAMSecondMoment.D1Spatial.spatial_white_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.spatial_white_le
#check @StratonovichHAMSecondMoment.D1Spatial.spatialPos_riesz_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.spatialPos_riesz_le
#check @StratonovichHAMSecondMoment.D1Spatial.spatialPos_white_le
#print axioms StratonovichHAMSecondMoment.D1Spatial.spatialPos_white_le
#check @StratonovichHAMSecondMoment.D1Spatial.d1_spatial_paper_riesz
#print axioms StratonovichHAMSecondMoment.D1Spatial.d1_spatial_paper_riesz
#check @StratonovichHAMSecondMoment.D1Spatial.d1_spatial_paper_white
#print axioms StratonovichHAMSecondMoment.D1Spatial.d1_spatial_paper_white
#check @StratonovichHAMSecondMoment.D1Spatial.selfPair
#print axioms StratonovichHAMSecondMoment.D1Spatial.selfPair
#check @StratonovichHAMSecondMoment.D1Spatial.selfPair_mem
#print axioms StratonovichHAMSecondMoment.D1Spatial.selfPair_mem
#check @StratonovichHAMSecondMoment.D1Spatial.openers_selfPair
#print axioms StratonovichHAMSecondMoment.D1Spatial.openers_selfPair
#check @StratonovichHAMSecondMoment.D1Spatial.closers_selfPair
#print axioms StratonovichHAMSecondMoment.D1Spatial.closers_selfPair
#check @StratonovichHAMSecondMoment.D1Spatial.spatialPair_selfPair
#print axioms StratonovichHAMSecondMoment.D1Spatial.spatialPair_selfPair

/-! Consumer: the form `P:d1-upper` uses, the spatial part of a diagram at the time
increments of a point of the time simplices, Riesz and white. -/

open MeasureTheory StratonovichHAMSecondMoment DiagramModel D1Spatial in
theorem audit_consumer_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    {m n k : ℕ} (hk : 1 ≤ k) (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)}
    (hD : D ∈ Pi2 m n) {ε : ℝ} (hε : 0 < ε) {t : ℝ} {s : Fin (m + n) → ℝ}
    (hs : s ∈ twoSimplex m n t) (hsum : ∑ i, incr m s i ≤ 2 * t) :
    spatial (WaveGreen.waveGreen 1) (covEps (volume.withDensity (HigherRieszTwo.riesz c α)) ε)
        m D (incr m s) ≤
      ENNReal.ofReal (Ksp c α ^ k * t ^ ((2 - α) * k) / (k : ℝ) ^ ((2 - α) * k)) :=
  (spatial_riesz_le hc hα0 hα1 hmn hD hε fun i => (incr_pos hs i).le).2 hk t hsum

open MeasureTheory StratonovichHAMSecondMoment DiagramModel D1Spatial in
theorem audit_consumer_white {c : ℝ} (hc : 0 ≤ c) {m n k : ℕ} (hk : 1 ≤ k)
    (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : ℝ}
    (hε : 0 < ε) {t : ℝ} {s : Fin (m + n) → ℝ} (hs : s ∈ twoSimplex m n t)
    (hsum : ∑ i, incr m s i ≤ 2 * t) :
    spatial (WaveGreen.waveGreen 1) (covEps (WhiteModel.whiteCov c) ε) m D (incr m s) ≤
      ENNReal.ofReal (c ^ k * t ^ k / (k : ℝ) ^ k) :=
  (spatial_white_le hc hmn hD hε fun i => (incr_pos hs i).le).2 hk t hsum

#print axioms audit_consumer_riesz
#print axioms audit_consumer_white
