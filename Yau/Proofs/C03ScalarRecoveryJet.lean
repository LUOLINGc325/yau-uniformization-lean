import Yau.Proofs.P03HolomorphicL2Decay

/-! A fixed-ball derivative estimate, with its constant chosen before the holomorphic function. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff
namespace Yau.Proofs.C03Aux.ScalarRecovery
open Yau Yau.NodeProofs.P03Aux
variable {n : ℕ}

theorem exists_derivative_L2_bound (R : ℝ) (hR : 0 < R) :
    ∃ D : ℝ, 0 < D ∧ ∀ h : ComplexVector n → ℂ, Differentiable ℂ h →
      ‖fderiv ℂ h 0‖ ≤ D * Real.sqrt
        (∫ z in closedBall (0 : ComplexVector n) R, ‖h z‖ ^ 2) := by
  obtain ⟨C, hC, hkernel⟩ := exists_holomorphic_jet_L1_bound (n := n) 1
  let t := R / 8
  have ht : 0 < t := by dsimp [t]; positivity
  let χ : ContDiffBump (0 : ComplexVector n) :=
    { rIn := R / 2, rOut := R, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let K := ((t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * t⁻¹ * C) *
    Real.sqrt ((volume : Measure (ComplexVector n)).real (closedBall 0 t))
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro h hh
  let F : ComplexVector n → ℂ := fun z => χ z • h z
  have hFc : Continuous F := χ.continuous.smul hh.continuous
  have hFs : HasCompactSupport F := χ.hasCompactSupport.smul_right
  have hFh (z : ComplexVector n) (hz : z ∈ closedBall 0 (R / 2)) : F z = h z := by
    simp [F, χ.one_of_mem_closedBall hz]
  have hHol : DifferentiableOn ℂ F (ball 0 (3 * t)) := by
    apply hh.differentiableOn.congr
    intro z hz
    apply hFh
    exact closedBall_subset_closedBall (by dsimp [t]; linarith)
      (ball_subset_closedBall hz)
  have hgerm : F =ᶠ[𝓝 (0 : ComplexVector n)] h := by
    filter_upwards [ball_mem_nhds (0 : ComplexVector n) (by positivity : 0 < R / 2)] with z hz
    exact hFh z (ball_subset_closedBall hz)
  have hfi : Integrable F volume := hFc.integrable_of_hasCompactSupport hFs
  have hfp : MemLp F 2 volume := hFc.memLp_of_hasCompactSupport hFs
  let ν := (volume : Measure (ComplexVector n)).restrict (closedBall 0 t)
  letI : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using
      (isCompact_closedBall (0 : ComplexVector n) t).measure_lt_top⟩
  have hcs := integral_norm_le_sqrt_L2 ν (hfp.mono_measure Measure.restrict_le_self)
  have hL2 : (∫ z in closedBall (0 : ComplexVector n) t, ‖F z‖ ^ 2) ≤
      ∫ z in closedBall (0 : ComplexVector n) R, ‖h z‖ ^ 2 := by
    calc
      _ = ∫ z in closedBall (0 : ComplexVector n) t, ‖h z‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_closedBall
        intro z hz
        change ‖F z‖ ^ 2 = ‖h z‖ ^ 2
        rw [hFh z (closedBall_subset_closedBall (by dsimp [t]; linarith) hz)]
      _ ≤ _ := setIntegral_mono_set
        ((hh.continuous.norm.pow 2).continuousOn.integrableOn_compact
          (isCompact_closedBall (0 : ComplexVector n) R))
        (Eventually.of_forall (fun z => sq_nonneg ‖h z‖))
        (Filter.Eventually.of_forall (fun z hz =>
          closedBall_subset_closedBall (by dsimp [t]; linarith) hz))
  have hb := hkernel F hFc hfi 0 t ht hHol
  rw [norm_iteratedFDeriv_one, (hgerm.fderiv_eq (𝕜 := ℝ))] at hb
  rw [(hh 0).fderiv_restrictScalars ℝ, ContinuousLinearMap.norm_restrictScalars] at hb
  have hbound : ‖fderiv ℂ h 0‖ ≤ K * Real.sqrt
      (∫ z in closedBall (0 : ComplexVector n) R, ‖h z‖ ^ 2) := by
    calc
      _ ≤ ((t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * t⁻¹ * C) *
          (Real.sqrt (∫ z in closedBall (0 : ComplexVector n) t, ‖F z‖ ^ 2) *
            Real.sqrt (ν.real univ)) := by
        simpa only [pow_one] using hb.trans
          (mul_le_mul_of_nonneg_left hcs (by positivity))
      _ ≤ ((t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * t⁻¹ * C) *
          (Real.sqrt (∫ z in closedBall (0 : ComplexVector n) R, ‖h z‖ ^ 2) *
            Real.sqrt (ν.real univ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hL2) (Real.sqrt_nonneg _))
          (by positivity)
      _ = _ := by
        dsimp [K, ν]
        simp only [measureReal_def, Measure.restrict_apply_univ]
        ring
  exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

end Yau.Proofs.C03Aux.ScalarRecovery
