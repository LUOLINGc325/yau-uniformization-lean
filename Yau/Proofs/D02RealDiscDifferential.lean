import Yau.Proofs.D02RadialVelocity

/-! The actual real derivative of an original holomorphic disc, in every
real parameter direction, has exactly the same Hermitian energy density. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem realDiscDerivative_chart {f : ℂ → M.Carrier} {z : ℂ}
    (hc : ContinuousAt f z)
    (hd : DifferentiableAt ℝ (fun w => chartPt (f z) (f w)) z) (v : ℂ) :
    L12Aux.realTangentEquiv (f z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ComplexVector n) f z
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) =
      (tangentSpaceCastModel (ComplexModel n) (f z)).symm
        (fderiv ℝ (fun w => chartPt (f z) (f w)) z v) := by
  have hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ComplexVector n) f z := by
    rw [mdifferentiableAt_iff]
    refine ⟨hc, ?_⟩
    convert hd.differentiableWithinAt using 1 <;>
      simp [writtenInExtChartAt, L12Aux.real_extChartAt_eq, mfld_simps] <;> rfl
  rw [hf.mfderiv]
  simp [writtenInExtChartAt, L12Aux.real_extChartAt_eq, L12Aux.realTangentEquiv, mfld_simps]
  rfl

theorem holomorphicDisc_contMDiffAt_real {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ComplexVector n) 1 f z := by
  letI := L12Aux.manifold_realSmooth M
  have hn : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  rw [contMDiffAt_iff]
  refine ⟨(hf.contMDiffAt hn).continuousAt, ?_⟩
  simp only [L12Aux.real_extChartAt_eq, mfld_simps, contDiffWithinAt_univ]
  exact ((disc_chart_contDiffAt hf hz).restrict_scalars ℝ).of_le (by simp)

theorem realDiscDerivative_eq_complex {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) (v : ℂ) :
    L12Aux.realTangentEquiv (f z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ComplexVector n) f z
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) =
      v • physicalCurveDerivative f z := by
  have hn : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hcomplex := (disc_chart_contDiffAt hf hz).differentiableAt (by simp)
  have hreal := hcomplex.hasFDerivAt.restrictScalars ℝ
  rw [realDiscDerivative_chart (hf.contMDiffAt hn).continuousAt hreal.differentiableAt v,
    hreal.fderiv]
  change (tangentSpaceCastModel (ComplexModel n) (f z)).symm
    (fderiv ℂ (fun w => chartPt (f z) (f w)) z v) = _
  rw [← L12Aux.chartVec_self]
  have hlin : fderiv ℂ (fun w => chartPt (f z) (f w)) z v =
      v • fderiv ℂ (fun w => chartPt (f z) (f w)) z 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (fderiv ℂ (fun w => chartPt (f z) (f w)) z).map_smul v (1 : ℂ)
  rw [hlin, chartVec_smul, ← physicalCurveDerivative_coords hf hz,
    chartVec_tangentCoords _ _ (mem_extChartAt_source (f z))]

theorem realDiscDerivative_norm (g : HermitianField M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) (v : ℂ) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (f z)
    ‖mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ComplexVector n) f z
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)‖ =
        ‖v‖ * Real.sqrt (closedDiscDensity g f z) := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (f z)
  rw [L12Aux.underlyingRealTangent_norm, realDiscDerivative_eq_complex hf hz v,
    G01Aux.hermitianNormSq_smul, closedDiscDensity_eq_physical g hf hz]
  rw [Complex.normSq_eq_norm_sq]
  have heq : 2 * (‖v‖ ^ 2 * hermitianNormSq (g (f z)) (physicalCurveDerivative f z)) =
      ‖v‖ ^ 2 * (2 * hermitianNormSq (g (f z)) (physicalCurveDerivative f z)) := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

end Yau.NodeProofs.D02Aux
