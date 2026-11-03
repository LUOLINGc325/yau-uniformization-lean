import Yau.Proofs.V03DiscIntegralVariation

/-! Actual higher parameter derivatives commute with the original disc
integral. An integrable pointwise derivative majorant controls the operator norm. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

theorem compactParamIntegral_contDiffOn {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {U : Set ℂ} (hU : IsOpen U) {J : Set Q} [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
    (hJ : UniqueDiffOn ℝ J) (μ : Measure J) [IsFiniteMeasure μ]
    {f : ℂ × Q → ℝ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ J)) :
    ContDiffOn ℝ ∞ (fun z => compactIntegralL μ (compactParamTrace hf.continuousOn z)) U :=
  (compactIntegralL μ).contDiff.comp_contDiffOn (compactParamTrace_contDiffOn hU hJ hf)

theorem iteratedFDeriv_compactParamIntegral_apply {Q : Type}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {U : Set ℂ} (hU : IsOpen U)
    {J : Set Q} [CompactSpace J] [MeasurableSpace J] [BorelSpace J] (hJ : UniqueDiffOn ℝ J)
    (μ : Measure J) [IsFiniteMeasure μ] {f : ℂ × Q → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ J)) {z : ℂ} (hz : z ∈ U)
    (k : ℕ) (v : Fin k → ℂ) :
    iteratedFDeriv ℝ k (fun p => compactIntegralL μ (compactParamTrace hf.continuousOn p)) z v =
      ∫ θ : J, iteratedFDeriv ℝ k (fun p => f (p, θ)) z v ∂μ := by
  let T := compactParamTrace hf.continuousOn
  have hT : ContDiffAt ℝ ∞ T z :=
    (compactParamTrace_contDiffOn hU hJ hf).contDiffAt (hU.mem_nhds hz)
  have hL := (compactIntegralL μ).iteratedFDeriv_comp_left hT (i := k) (by simp)
  change iteratedFDeriv ℝ k (compactIntegralL μ ∘ T) z v = _
  rw [hL, ContinuousLinearMap.compContinuousMultilinearMap_coe]
  change (∫ θ : J, iteratedFDeriv ℝ k T z v θ ∂μ) = _
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    have hpoint : (fun p => T p θ) =ᶠ[𝓝 z] (fun p => f (p, θ)) := by
      filter_upwards [hU.mem_nhds hz] with p hp
      exact compactParamTrace_apply hf.continuousOn hp θ
    have hEval := (ContinuousMap.evalCLM ℝ θ).iteratedFDeriv_comp_left hT (i := k) (by simp)
    have heval := congrArg (fun A => A v) hEval
    simp only [Function.comp_def, ContinuousMap.evalCLM_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe] at heval
    rw [← heval]
    exact congrArg (fun A => A v) ((hpoint.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds)

theorem norm_iteratedFDeriv_compactParamIntegral_le {Q : Type}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {U : Set ℂ} (hU : IsOpen U)
    {J : Set Q} [CompactSpace J] [MeasurableSpace J] [BorelSpace J] (hJ : UniqueDiffOn ℝ J)
    (μ : Measure J) [IsFiniteMeasure μ] {f : ℂ × Q → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ J)) {z : ℂ} (hz : z ∈ U) (k : ℕ)
    {w : J → ℝ} (hw : Integrable w μ) (hw0 : ∀ θ, 0 ≤ w θ)
    (hb : ∀ θ : J, ‖iteratedFDeriv ℝ k (fun p => f (p, θ)) z‖ ≤ w θ) :
    ‖iteratedFDeriv ℝ k
      (fun p => compactIntegralL μ (compactParamTrace hf.continuousOn p)) z‖ ≤ ∫ θ : J, w θ ∂μ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (integral_nonneg hw0)
  intro v
  rw [iteratedFDeriv_compactParamIntegral_apply hU hJ μ hf hz k v]
  have hmajor := norm_integral_le_of_norm_le (hw.mul_const (∏ i, ‖v i‖))
    (Eventually.of_forall (fun θ => (ContinuousMultilinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right (hb θ) (Finset.prod_nonneg (fun i _ => norm_nonneg _)))))
  simpa only [integral_mul_const] using hmajor

theorem discTraceIntegralL_eq (u : C(ClosedDiscTraceDomain, ℝ)) (g : ℂ → ℝ)
    (hug : ∀ ζ : ClosedDiscTraceDomain, u ζ = g ζ) :
    discTraceIntegralL u = ∫ ζ in Metric.ball (0 : ℂ) 1, g ζ := by
  change (∫ ζ : ClosedDiscTraceDomain, u ζ ∂discInteriorTraceMeasure) = _
  calc
    _ = ∫ ζ : ClosedDiscTraceDomain, g ζ ∂discInteriorTraceMeasure :=
      integral_congr_ae (Eventually.of_forall hug)
    _ = _ := by
      rw [discInteriorTraceMeasure, integral_subtype_comap
        (μ := volume.restrict (Metric.ball (0 : ℂ) 1))
        (s := ClosedDiscTraceDomain) measurableSet_closedBall g,
        Measure.restrict_restrict measurableSet_closedBall,
        Set.inter_eq_right.mpr Metric.ball_subset_closedBall]

theorem iteratedFDeriv_discIntegral_apply {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℂ → ℝ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain))
    {z : ℂ} (hz : z ∈ U) (k : ℕ) (v : Fin k → ℂ) :
    iteratedFDeriv ℝ k (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ)) z v =
      ∫ ζ in Metric.ball (0 : ℂ) 1, iteratedFDeriv ℝ k (fun p => f (p, ζ)) z v := by
  let T := compactParamTrace hf.continuousOn
  have hT : ContDiffAt ℝ ∞ T z :=
    (compactParamTrace_contDiffOn hU uniqueDiffOn_real_closedDisc hf).contDiffAt (hU.mem_nhds hz)
  have heq : (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ)) =ᶠ[𝓝 z]
      (fun p => discTraceIntegralL (T p)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact (discTraceIntegral_compactParamTrace hf hp).symm
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  have hL := discTraceIntegralL.iteratedFDeriv_comp_left hT (i := k) (by simp)
  change iteratedFDeriv ℝ k (discTraceIntegralL ∘ T) z v = _
  rw [hL, ContinuousLinearMap.compContinuousMultilinearMap_coe]
  apply discTraceIntegralL_eq
  intro ζ
  have hpoint : (fun p => T p ζ) =ᶠ[𝓝 z] (fun p => f (p, ζ)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact compactParamTrace_apply hf.continuousOn hp ζ
  have hEval := (ContinuousMap.evalCLM ℝ ζ).iteratedFDeriv_comp_left hT (i := k) (by simp)
  have heval := congrArg (fun A => A v) hEval
  simp only [Function.comp_def, ContinuousMap.evalCLM_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe] at heval
  rw [← heval]
  exact congrArg (fun A => A v) ((hpoint.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds)

theorem norm_iteratedFDeriv_discIntegral_le {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℂ → ℝ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain))
    {z : ℂ} (hz : z ∈ U) (k : ℕ) {w : ℂ → ℝ}
    (hw : IntegrableOn w (Metric.ball (0 : ℂ) 1))
    (hw0 : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, 0 ≤ w ζ)
    (hb : ∀ ζ ∈ Metric.ball (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ k (fun p => f (p, ζ)) z‖ ≤ w ζ) :
    ‖iteratedFDeriv ℝ k (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ)) z‖ ≤
      ∫ ζ in Metric.ball (0 : ℂ) 1, w ζ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (setIntegral_nonneg measurableSet_ball hw0)
  intro v
  rw [iteratedFDeriv_discIntegral_apply hU hf hz k v]
  have hmajor := norm_integral_le_of_norm_le
    (hw.mul_const (∏ i, ‖v i‖)) (ae_restrict_of_forall_mem measurableSet_ball (fun ζ hζ =>
      (ContinuousMultilinearMap.le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right (hb ζ hζ) (Finset.prod_nonneg (fun i _ => norm_nonneg _)))))
  simpa only [integral_mul_const] using hmajor

end Yau.Blueprint.V02AreaTaylorProof
