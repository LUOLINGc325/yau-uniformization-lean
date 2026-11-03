import Yau.Proofs.P03HolomorphicKernelJets
import Yau.Proofs.P03LocalL2Bounds
import Yau.Proofs.P03ApproxKernels

open scoped Topology ContDiff ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- A genuine small-ball L² decay estimate forces the native real Taylor
tensors to vanish. The estimate is proved by radial reproduction and actual
iterated convolution differentiation, without a symmetry premise. -/
theorem real_jets_zero_of_L2_decay (f : ComplexVector n → ℂ) (hc : Continuous f)
    (hfc : HasCompactSupport f) (a : ComplexVector n) (R : ℝ) (hR : 0 < R)
    (hH : DifferentiableOn ℂ f (Metric.ball a R)) (k : ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hL2 : ∀ t : ℝ, 0 < t → t < R →
      (∫ z in Metric.closedBall a t, ‖f z‖ ^ 2) ≤ D * t ^ (2 * (n + k + 1))) :
    ∀ j ≤ k, iteratedFDeriv ℝ j f a = 0 := by
  intro j hj
  obtain ⟨C, hC, hkernel⟩ := exists_holomorphic_jet_L1_bound (n := n) j
  let V := Real.sqrt ((volume : Measure (ComplexVector n)).real (Metric.closedBall 0 1))
  let A := C * Real.sqrt D * V
  have hi : Integrable f volume := hc.integrable_of_hasCompactSupport hfc
  have hp : MemLp f 2 volume := hc.memLp_of_hasCompactSupport hfc
  have hbound (t : ℝ) (ht : 0 < t) (htR : 3 * t < R) :
      ‖iteratedFDeriv ℝ j f a‖ ≤ A * t ^ (k + 1 - j) := by
    let ν := (volume : Measure (ComplexVector n)).restrict (Metric.closedBall a t)
    letI : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using
      (isCompact_closedBall a t).measure_lt_top⟩
    have hcs := integral_norm_le_sqrt_L2 ν (hp.mono_measure Measure.restrict_le_self)
    have hvol : Real.sqrt (ν.real univ) = t ^ n * V := by
      simpa only [ν, measureReal_def, Measure.restrict_apply_univ, V] using
        sqrt_volume_closedBall a ht.le
    have hsqrt : Real.sqrt (∫ z in Metric.closedBall a t, ‖f z‖ ^ 2) ≤
        t ^ (n + k + 1) * Real.sqrt D := by
      calc
        _ ≤ Real.sqrt (D * t ^ (2 * (n + k + 1))) := Real.sqrt_le_sqrt (hL2 t ht (by linarith))
        _ = _ := by
          rw [Real.sqrt_mul hD, mul_comm 2 (n + k + 1), pow_mul,
            Real.sqrt_sq (pow_nonneg ht.le _)]
          ring
    have hB := hkernel f hc hi a t ht (hH.mono (Metric.ball_subset_ball htR.le))
    rw [complexVector_real_dimension] at hB
    calc
      _ ≤ ((t ^ (2 * n))⁻¹ * (t⁻¹) ^ j * C) *
          (Real.sqrt (∫ z in Metric.closedBall a t, ‖f z‖ ^ 2) * Real.sqrt (ν.real univ)) :=
        hB.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
      _ ≤ ((t ^ (2 * n))⁻¹ * (t⁻¹) ^ j * C) *
          ((t ^ (n + k + 1) * Real.sqrt D) * (t ^ n * V)) := by
        rw [hvol]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsqrt (by positivity)) (by positivity)
      _ = A * t ^ (k + 1 - j) := by
        dsimp only [A]
        rw [inv_pow]
        field_simp
        have he : 2 * n + j + (k + 1 - j) = n + k + 1 + n := by omega
        have hp : t ^ (2 * n + j) * t ^ (k + 1 - j) = t ^ (n + k + 1) * t ^ n := by
          rw [← pow_add, he, pow_add]
        calc
          _ = (C * Real.sqrt D * V) * (t ^ (n + k + 1) * t ^ n) := by ring
          _ = (C * Real.sqrt D * V) * (t ^ (2 * n + j) * t ^ (k + 1 - j)) := by rw [hp]
          _ = _ := by ring
  have hpow : k + 1 - j ≠ 0 := by omega
  have hlim : Tendsto (fun i => A * approxRadius (R / 4) i ^ (k + 1 - j)) atTop (𝓝 0) := by
    simpa only [zero_pow hpow, mul_zero] using
      ((approxRadius_tendsto (R / 4)).pow (k + 1 - j)).const_mul A
  have hle : ‖iteratedFDeriv ℝ j f a‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall fun i => by
      have hr := approxRadius_le (by positivity : 0 < R / 4) i
      exact hbound _ (approxRadius_pos (by positivity) i) (by linarith))
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

end Yau.NodeProofs.P03Aux
