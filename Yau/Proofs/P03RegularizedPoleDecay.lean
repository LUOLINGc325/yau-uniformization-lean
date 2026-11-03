import Yau.Proofs.P03PoleSequence
import Yau.Proofs.P03Measure

open scoped Topology ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

theorem regularized_log_nat_lower (m : ℕ) {q Q : ℝ} (hq : 0 < q) (hQ : q ≤ Q) :
    1 ≤ Q ^ m * Real.exp (-((m : ℝ) * Real.log q)) := by
  have he : Real.exp ((m : ℝ) * Real.log q) = q ^ m := by
    rw [Real.exp_nat_mul, Real.exp_log hq]
  have hprod : q ^ m * Real.exp (-((m : ℝ) * Real.log q)) = 1 := by
    rw [← he, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← hprod]
  exact mul_le_mul_of_nonneg_right (by gcongr) (Real.exp_pos _).le

/-- The same function obeying every regularized logarithmic estimate has
the required small-ball L² decay. The parameter is selected after the radius,
while the function and the finite bound remain fixed. -/
theorem L2_decay_of_regularized_pole_bounds {n : ℕ} (f : ComplexVector n → ℂ)
    (a : ComplexVector n) (R : ℝ) (hR : 0 < R) (m : ℕ)
    (hm : AEStronglyMeasurable f ((volume : Measure (ComplexVector n)).restrict
      (Metric.closedBall a R))) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j : ℕ,
      (∫⁻ z in Metric.closedBall a R, ENNReal.ofReal (‖f z‖ ^ 2 *
        Real.exp (-((m : ℝ) * modelLogPole a (poleEpsilon j) z)))) ≤ ENNReal.ofReal B) :
    ∀ t : ℝ, 0 < t → t < R →
      (∫ z in Metric.closedBall a t, ‖f z‖ ^ 2) ≤ ((2 : ℝ) ^ m * B) * t ^ (2 * m) := by
  intro t ht htR
  have heps : ∀ᶠ j in atTop, poleEpsilon j < t ^ 2 :=
    poleEpsilon_tendsto_zero.eventually (gt_mem_nhds (sq_pos_of_pos ht))
  obtain ⟨j, hj⟩ := heps.exists
  let K := Metric.closedBall a t
  let W : ComplexVector n → ℝ := fun z => ‖f z‖ ^ 2 *
    Real.exp (-((m : ℝ) * modelLogPole a (poleEpsilon j) z))
  have hs : K ⊆ Metric.closedBall a R := Metric.closedBall_subset_closedBall htR.le
  have hpoint (z : ComplexVector n) (hz : z ∈ K) :
      ‖f z‖ ^ 2 ≤ (2 * t ^ 2) ^ m * W z := by
    have hn : ‖z - a‖ ≤ t := by simpa only [K, Metric.mem_closedBall, dist_eq_norm] using hz
    have hq : ‖z - a‖ ^ 2 + poleEpsilon j ≤ 2 * t ^ 2 := by
      nlinarith [norm_nonneg (z - a)]
    have hlow := regularized_log_nat_lower m
      (show 0 < ‖z - a‖ ^ 2 + poleEpsilon j from add_pos_of_nonneg_of_pos (sq_nonneg _) (poleEpsilon_pos j)) hq
    have hmul := mul_le_mul_of_nonneg_left hlow (sq_nonneg ‖f z‖)
    change ‖f z‖ ^ 2 ≤ (2 * t ^ 2) ^ m *
      (‖f z‖ ^ 2 * Real.exp (-((m : ℝ) * Real.log (‖z - a‖ ^ 2 + poleEpsilon j))))
    nlinarith only [hmul]
  have hlin : (∫⁻ z in K, ENNReal.ofReal (‖f z‖ ^ 2)) ≤
      ENNReal.ofReal (((2 : ℝ) ^ m * B) * t ^ (2 * m)) := by
    calc
      _ ≤ ∫⁻ z in K, ENNReal.ofReal ((2 * t ^ 2) ^ m * W z) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with z hz
        exact ENNReal.ofReal_le_ofReal (hpoint z hz)
      _ = ENNReal.ofReal ((2 * t ^ 2) ^ m) * ∫⁻ z in K, ENNReal.ofReal (W z) := by
        simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * t ^ 2) ^ m)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((2 * t ^ 2) ^ m) * ENNReal.ofReal B :=
        mul_le_mul_right ((lintegral_mono_set hs).trans (hb j)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * t ^ 2) ^ m)]
        apply congrArg ENNReal.ofReal
        rw [mul_pow, ← pow_mul]
        ring
  let ν := (volume : Measure (ComplexVector n)).restrict K
  have hms : AEStronglyMeasurable f ν := hm.mono_measure (Measure.restrict_mono hs le_rfl)
  have hint : Integrable (fun z => ‖f z‖ ^ 2) ν :=
    ⟨(hms.norm.aemeasurable.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg ‖f z‖)).mpr
        (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => sq_nonneg ‖f z‖)] at hlin
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg ‖f z‖),
    ENNReal.toReal_ofReal (show 0 ≤ ((2 : ℝ) ^ m * B) * t ^ (2 * m) by positivity)] using hreal

end Yau.NodeProofs.P03Aux
