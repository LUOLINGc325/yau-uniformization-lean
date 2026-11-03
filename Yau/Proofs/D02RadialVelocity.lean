import Yau.Proofs.D02AreaDensity
import Yau.Proofs.D02PolarEnergy

/-! The actual real radial velocity equals the original complex disc
derivative multiplied by a unit complex number. No new speed is supplied. -/

open scoped Manifold Topology ContDiff
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def radialCurve (f : ℂ → M.Carrier) (θ : ℝ) (r : ℝ) : M.Carrier := f (polarRay r θ)

theorem polarRay_hasDerivAt (θ r : ℝ) :
    HasDerivAt (fun s => polarRay s θ) (polarRay 1 θ) r := by
  convert (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const
    ((Real.cos θ : ℂ) + Real.sin θ * Complex.I) using 1 <;>
    simp [polarRay, Complex.polarCoord_symm_apply]

theorem polarRay_contDiff (θ : ℝ) : ContDiff ℝ ∞ (fun r => polarRay r θ) := by
  simp only [polarRay, Complex.polarCoord_symm_apply]
  have hc : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  exact hc.mul contDiff_const

theorem radialCurve_continuousOn {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (θ : ℝ) :
    ContinuousOn (radialCurve f θ) (Icc (0 : ℝ) 1) := by
  apply hf.continuousOn.comp (polarRay_contDiff θ).continuous.continuousOn
  intro r hr
  simp only [Metric.mem_closedBall, dist_zero_right, polarRay_norm, abs_of_nonneg hr.1]
  exact hr.2

theorem disc_chart_contDiffAt {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ContDiffAt ℂ ∞ (fun w => chartPt (f z) (f w)) z := by
  have hn : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  exact ((contMDiffWithinAt_iff_target.mp (hf z (Metric.ball_subset_closedBall hz))).2.contDiffWithinAt).contDiffAt hn

theorem radialCurve_chart_contDiffAt {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun s => chartPt (radialCurve f θ r) (radialCurve f θ s)) r := by
  have hz : polarRay r θ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, polarRay_norm, abs_of_pos hr.1] using hr.2
  change ContDiffAt ℝ ∞ ((fun w => chartPt (f (polarRay r θ)) (f w)) ∘
    (fun s => polarRay s θ)) r
  exact ((disc_chart_contDiffAt hf hz).restrict_scalars ℝ).comp r
    (polarRay_contDiff θ).contDiffAt

theorem radialCurve_contMDiffAt_real {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (radialCurve f θ) r := by
  letI := L12Aux.manifold_realSmooth M
  rw [contMDiffAt_iff]
  refine ⟨(radialCurve_continuousOn hf θ).continuousAt (Icc_mem_nhds hr.1 hr.2), ?_⟩
  simp only [L12Aux.real_extChartAt_eq, mfld_simps, contDiffWithinAt_univ]
  exact (radialCurve_chart_contDiffAt hf θ hr).of_le (by simp)

/-- The original complex derivative in the actual chart centred at its value. -/
theorem physicalCurveDerivative_coords {f : ℂ → M.Carrier}
    (hf : IsHolomorphicDisc f) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    tangentCoords (f z) (f z) (physicalCurveDerivative f z) =
      fderiv ℂ (fun w => chartPt (f z) (f w)) z 1 := by
  have hn : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hd := (hf.contMDiffAt hn).mdifferentiableAt (by simp)
  have hc := mfderiv_comp_apply z
    (mdifferentiableAt_extChartAt (I := ComplexModel n) (mem_chart_source (ComplexVector n) (f z))) hd
    ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1)
  rw [mfderiv_eq_fderiv] at hc
  exact hc.symm

theorem radialCurve_velocity {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    L12Aux.realTangentEquiv (radialCurve f θ r)
      (L12Aux.realCurveVelocity (radialCurve f θ) r) =
        polarRay 1 θ • physicalCurveDerivative f (polarRay r θ) := by
  have hz : polarRay r θ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, polarRay_norm, abs_of_pos hr.1] using hr.2
  have hc := (radialCurve_continuousOn hf θ).continuousAt (Icc_mem_nhds hr.1 hr.2)
  have hd := ((disc_chart_contDiffAt hf hz).differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ
  have hdcomp := hd.comp_hasDerivAt r (polarRay_hasDerivAt θ r)
  rw [L12Aux.realCurveVelocity_chart hc
    ((radialCurve_chart_contDiffAt hf θ hr).differentiableAt (by simp))]
  rw [fderiv_apply_one_eq_deriv]
  change (tangentSpaceCastModel (ComplexModel n) (f (polarRay r θ))).symm
    (deriv ((fun w => chartPt (f (polarRay r θ)) (f w)) ∘ (fun s => polarRay s θ)) r) = _
  rw [hdcomp.deriv]
  have hcoords := physicalCurveDerivative_coords hf hz
  change (tangentSpaceCastModel (ComplexModel n) (f (polarRay r θ))).symm
    (fderiv ℂ (fun w => chartPt (f (polarRay r θ)) (f w)) (polarRay r θ) (polarRay 1 θ)) = _
  rw [← L12Aux.chartVec_self]
  have hlin : fderiv ℂ (fun w => chartPt (f (polarRay r θ)) (f w)) (polarRay r θ) (polarRay 1 θ) =
      polarRay 1 θ • fderiv ℂ (fun w => chartPt (f (polarRay r θ)) (f w)) (polarRay r θ) 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (fderiv ℂ (fun w => chartPt (f (polarRay r θ)) (f w)) (polarRay r θ)).map_smul (polarRay 1 θ) (1 : ℂ)
  rw [hlin, chartVec_smul, ← hcoords,
    chartVec_tangentCoords _ _ (mem_extChartAt_source (f (polarRay r θ)))]

theorem radialCurve_speed (g : HermitianField M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (θ : ℝ) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (radialCurve f θ r)
    ‖L12Aux.realCurveVelocity (radialCurve f θ) r‖ =
      Real.sqrt (closedDiscDensity g f (polarRay r θ)) := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (radialCurve f θ r)
  rw [L12Aux.underlyingRealTangent_norm, radialCurve_velocity hf θ hr,
    G01Aux.hermitianNormSq_smul]
  have hunit : Complex.normSq (polarRay 1 θ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, polarRay_norm]
    norm_num
  have hz : polarRay r θ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, polarRay_norm, abs_of_pos hr.1] using hr.2
  rw [hunit, one_mul, closedDiscDensity_eq_physical g hf hz]
  rfl

end Yau.NodeProofs.D02Aux
