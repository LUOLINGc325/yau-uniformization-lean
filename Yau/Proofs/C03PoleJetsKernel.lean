import Yau.Proofs.P03HolomorphicL2Decay

/-! At the critical exponent the first jet vanishes from an actual small-o
L2 bound. The coefficient sequence tends to zero; a fixed big-O constant
would not suffice for the linear jet. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal

namespace Yau.Proofs.C03Aux.PoleJets

open Yau Yau.NodeProofs.P03Aux
variable {n : ℕ}

theorem real_jets_zero_of_critical_sequence
    (f : ComplexVector n → ℂ) (hc : Continuous f) (hfc : HasCompactSupport f)
    (R : ℝ) (hH : DifferentiableOn ℂ f (Metric.ball (0 : ComplexVector n) R))
    (ρ : ℝ) (hρ : 0 < ρ) (hρR : 3 * ρ < R)
    (D : ℕ → ℝ) (hD : ∀ i, 0 ≤ D i) (hD0 : Tendsto D atTop (𝓝 0))
    (hL2 : ∀ i,
      (∫ z in Metric.closedBall (0 : ComplexVector n) (approxRadius ρ i), ‖f z‖ ^ 2) ≤
        D i * approxRadius ρ i ^ (2 * (n + 1))) :
    ∀ j ≤ 1, iteratedFDeriv ℝ j f 0 = 0 := by
  intro j hj
  obtain ⟨C, hC, hkernel⟩ := exists_holomorphic_jet_L1_bound (n := n) j
  let V := Real.sqrt ((volume : Measure (ComplexVector n)).real (Metric.closedBall 0 1))
  have hi : Integrable f volume := hc.integrable_of_hasCompactSupport hfc
  have hp : MemLp f 2 volume := hc.memLp_of_hasCompactSupport hfc
  have hbound (i : ℕ) : ‖iteratedFDeriv ℝ j f 0‖ ≤
      C * V * Real.sqrt (D i) * approxRadius ρ i ^ (1 - j) := by
    let t := approxRadius ρ i
    have ht : 0 < t := approxRadius_pos hρ i
    have htR : 3 * t < R := (mul_le_mul_of_nonneg_left (approxRadius_le hρ i) (by norm_num)).trans_lt hρR
    let ν := (volume : Measure (ComplexVector n)).restrict (Metric.closedBall 0 t)
    letI : IsFiniteMeasure ν := ⟨by
      simpa only [ν, Measure.restrict_apply_univ] using (isCompact_closedBall (0 : ComplexVector n) t).measure_lt_top⟩
    have hcs := integral_norm_le_sqrt_L2 ν (hp.mono_measure Measure.restrict_le_self)
    have hvol : Real.sqrt (ν.real univ) = t ^ n * V := by
      simpa only [ν, measureReal_def, Measure.restrict_apply_univ, V] using
        sqrt_volume_closedBall (0 : ComplexVector n) ht.le
    have hsqrt : Real.sqrt (∫ z in Metric.closedBall (0 : ComplexVector n) t, ‖f z‖ ^ 2) ≤
        t ^ (n + 1) * Real.sqrt (D i) := by
      calc
        _ ≤ Real.sqrt (D i * t ^ (2 * (n + 1))) := Real.sqrt_le_sqrt (hL2 i)
        _ = _ := by
          rw [Real.sqrt_mul (hD i), mul_comm 2 (n + 1), pow_mul,
            Real.sqrt_sq (pow_nonneg ht.le _)]
          ring
    have hB := hkernel f hc hi 0 t ht (hH.mono (Metric.ball_subset_ball htR.le))
    rw [complexVector_real_dimension] at hB
    calc
      _ ≤ ((t ^ (2 * n))⁻¹ * (t⁻¹) ^ j * C) *
          (Real.sqrt (∫ z in Metric.closedBall (0 : ComplexVector n) t, ‖f z‖ ^ 2) *
            Real.sqrt (ν.real univ)) := hB.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
      _ ≤ ((t ^ (2 * n))⁻¹ * (t⁻¹) ^ j * C) *
          ((t ^ (n + 1) * Real.sqrt (D i)) * (t ^ n * V)) := by
        rw [hvol]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsqrt (by positivity)) (by positivity)
      _ = C * V * Real.sqrt (D i) * t ^ (1 - j) := by
        rw [inv_pow]
        field_simp
        have he : 2 * n + j + (1 - j) = n + 1 + n := by omega
        have hpow : t ^ (2 * n + j) * t ^ (1 - j) = t ^ (n + 1) * t ^ n := by
          rw [← pow_add, he, pow_add]
        calc
          _ = (C * V * Real.sqrt (D i)) * (t ^ (n + 1) * t ^ n) := by ring
          _ = (C * V * Real.sqrt (D i)) * (t ^ (2 * n + j) * t ^ (1 - j)) := by rw [hpow]
          _ = _ := by ring
  have hlim : Tendsto (fun i => C * V * Real.sqrt (D i) * approxRadius ρ i ^ (1 - j))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, zero_mul, mul_zero, mul_assoc] using
      ((hD0.sqrt).mul ((approxRadius_tendsto ρ).pow (1 - j))).const_mul (C * V)
  have hz : ‖iteratedFDeriv ℝ j f 0‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))

end Yau.Proofs.C03Aux.PoleJets
