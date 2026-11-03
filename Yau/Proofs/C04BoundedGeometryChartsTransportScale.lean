import Yau.Proofs.C04BoundedGeometryChartsTransportRegularity
import Yau.LeafProofs.L12Exponential

/-! Genuine parallel transport under radial time rescaling. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff Bundle
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def transportVelocityScale (c : ℝ) (q : realTransportBundle M) : realTransportBundle M :=
  ⟨q.proj, (c • q.2.1, q.2.2)⟩

def transportVelocityScaleCLM (n : ℕ) (c : ℝ) :
    (ComplexVector n × (ComplexVector n × ComplexVector n)) →L[ℝ]
      (ComplexVector n × (ComplexVector n × ComplexVector n)) :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n × ComplexVector n)).prod
    (((c • ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).prod
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n))).comp
        (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n × ComplexVector n)))

theorem transportVelocityScaleCLM_apply (c : ℝ)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) :
    transportVelocityScaleCLM n c q = (q.1, (c • q.2.1, q.2.2)) := rfl

theorem realTransportChart_transportVelocityScale (c : ℝ) (x : M.Carrier)
    (q : realTransportBundle M) :
    realTransportChart x (transportVelocityScale c q) =
      transportVelocityScaleCLM n c (realTransportChart x q) := by
  apply Prod.ext
  · rfl
  · exact Prod.ext ((realTangentCoords x q.proj).map_smul c q.2.1) rfl

theorem transportVelocityScale_realTransportPoint (c : ℝ) (x : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) :
    transportVelocityScale c (realTransportPoint x q) =
      realTransportPoint x (transportVelocityScaleCLM n c q) := by
  change (⟨chartInv x q.1, (c • realFrameCLM x (chartInv x q.1) q.2.1,
      realFrameCLM x (chartInv x q.1) q.2.2)⟩ : realTransportBundle M) =
    ⟨chartInv x q.1, (realFrameCLM x (chartInv x q.1) (c • q.2.1),
      realFrameCLM x (chartInv x q.1) q.2.2)⟩
  exact congrArg (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) (chartInv x q.1) =>
    (⟨chartInv x q.1, (a, realFrameCLM x (chartInv x q.1) q.2.2)⟩ : realTransportBundle M))
    ((realFrameCLM x (chartInv x q.1)).map_smul c q.2.1).symm

theorem transportVelocityScale_eventually_eq_chart (c : ℝ)
    (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    transportVelocityScale c =ᶠ[𝓝 p]
      ((extChartAt (realTransportModel n) p).symm ∘ transportVelocityScaleCLM n c ∘
        extChartAt (realTransportModel n) p) := by
  letI := manifold_realSmooth M
  filter_upwards [extChartAt_source_mem_nhds (I := realTransportModel n) p] with q hq
  have hbase := (realTransportChart_source p q).mp hq
  have hz : (transportVelocityScaleCLM n c (realTransportChart p.proj q)).1 ∈ chartTarget p.proj := by
    exact (extChartAt (ComplexModel n) p.proj).map_source
      (by simpa only [extChartAt_source] using hbase)
  change transportVelocityScale c q = (extChartAt (realTransportModel n) p).symm
    (transportVelocityScaleCLM n c (extChartAt (realTransportModel n) p q))
  rw [realTransportChart_eq_extChartAt p q hbase,
    realTransportPoint_eq_extChartAt_symm p _ hz,
    ← transportVelocityScale_realTransportPoint, realTransportPoint_realTransportChart p.proj q hbase]

theorem transportVelocityScale_contMDiff (c : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiff (realTransportModel n) (realTransportModel n) ∞
      (transportVelocityScale (M := M) c) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  intro p
  have hz : transportVelocityScaleCLM n c (extChartAt (realTransportModel n) p p) ∈
      (extChartAt (realTransportModel n) p).target := by
    apply (realTransportChart_target p _).mpr
    rw [realTransportChart_eq_extChartAt p p (mem_chart_source _ _)]
    exact mem_extChartAt_target p.proj
  have hi := contMDiffWithinAt_extChartAt_symm_range
    (I := realTransportModel n) (n := ∞) p hz
  rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hi
  have hm : ContMDiff 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n))
      𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) ∞ (transportVelocityScaleCLM n c) :=
    (transportVelocityScaleCLM n c).contDiff.contMDiff
  have hp : ContMDiffAt (realTransportModel n) 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) ∞
      (extChartAt (realTransportModel n) p) p := contMDiffAt_extChartAt
  exact (hi.comp p ((hm _).comp p hp)).congr_of_eventuallyEq
    (transportVelocityScale_eventually_eq_chart c p)

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_transportVelocityScale (c : ℝ)
    (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    mfderiv (realTransportModel n) (realTransportModel n) (transportVelocityScale c) p = transportVelocityScaleCLM n c := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  have hf := (transportVelocityScale_contMDiff (M := M) c p).mdifferentiableAt (by simp)
  have heq : writtenInExtChartAt (realTransportModel n) (realTransportModel n) p (transportVelocityScale c)
      =ᶠ[𝓝 (extChartAt (realTransportModel n) p p)] transportVelocityScaleCLM n c := by
    filter_upwards [(isOpen_extChartAt_target (I := realTransportModel n) p).mem_nhds
      (mem_extChartAt_target p)] with q hq
    have hz := (realTransportChart_target p q).mp hq
    have hz' : (transportVelocityScaleCLM n c q).1 ∈ chartTarget p.proj := hz
    have hsource : (realTransportPoint p.proj (transportVelocityScaleCLM n c q)).proj ∈
        (chartAt (ComplexVector n) p.proj).source := by
      simpa only [realTransportPoint, extChartAt_source, chartInv] using
        (extChartAt (ComplexModel n) p.proj).map_target hz'
    change extChartAt (realTransportModel n) p
      (transportVelocityScale c ((extChartAt (realTransportModel n) p).symm q)) = transportVelocityScaleCLM n c q
    rw [realTransportPoint_eq_extChartAt_symm p q hz, transportVelocityScale_realTransportPoint,
      realTransportChart_eq_extChartAt p _ hsource]
    exact realTransportChart_realTransportPoint p.proj _ hz'
  rw [hf.mfderiv_abuse, ModelWithCorners.range_eq_univ, fderivWithin_univ,
    heq.fderiv_eq, (transportVelocityScaleCLM n c).hasFDerivAt.fderiv]


theorem mfderiv_transportVelocityScale_spray (g : SmoothMetric M) (c : ℝ)
    (q : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    mfderiv (realTransportModel n) (realTransportModel n) (transportVelocityScale c) q
      (c • realParallelTransportSpray g q) =
        realParallelTransportSpray g (transportVelocityScale c q) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  rw [mfderiv_transportVelocityScale]
  change transportVelocityScaleCLM n c
      (c • chartParallelTransportField g.form q.proj (realTransportChart q.proj q)) =
    chartParallelTransportField g.form q.proj (realTransportChart q.proj (transportVelocityScale c q))
  rw [realTransportChart_transportVelocityScale]
  simp only [transportVelocityScaleCLM_apply, chartParallelTransportField,
    Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, map_smul, ContinuousLinearMap.smul_apply, smul_neg]

theorem realParallelTransport_rescale (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) (c : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurve γ (realParallelTransportSpray g) →
      IsMIntegralCurve (transportVelocityScale c ∘ γ ∘ (· * c)) (realParallelTransportSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro hγ t
  have hm := hγ.comp_mul c
  have hH := ((transportVelocityScale_contMDiff (M := M) c (γ (t * c))).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have hcomp := hH.comp t (hm t)
  apply hcomp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change mfderiv (realTransportModel n) (realTransportModel n) (transportVelocityScale c) (γ (t * c))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (c • realParallelTransportSpray g (γ (t * c)))) a) =
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (realParallelTransportSpray g (transportVelocityScale c (γ (t * c))))) a
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
  rw [map_smul, mfderiv_transportVelocityScale_spray]

theorem realParallelTransportFlow_rescale (g : SmoothMetric M) (c : ℝ)
    (q : realTransportBundle M) (t : ℝ) :
    realParallelTransportFlow g (transportVelocityScale c q) t =
      transportVelocityScale c (realParallelTransportFlow g q (t * c)) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  have H := realParallelTransportFlow_unique g (transportVelocityScale c q)
    (transportVelocityScale c ∘ realParallelTransportFlow g q ∘ (· * c))
    (by simp [realParallelTransportFlow_zero])
    (realParallelTransport_rescale g (realParallelTransportFlow g q) c
      (realParallelTransportFlow_integral g q))
  exact (congrFun H t).symm

theorem realParallelLift_scaled_velocity (g : SmoothMetric M) (p : M.Carrier)
    (v w : TangentSpace 𝓘(ℝ, ComplexVector n) p) (t : ℝ) :
    realParallelLift g (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) w 1 =
      realParallelLift g (⟨p, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) w t := by
  have H := congrArg realTransportVector
    (realParallelTransportFlow_rescale g t (⟨p, (v, w)⟩ : realTransportBundle M) 1)
  rw [one_mul] at H
  simpa only [realParallelLift, transportVelocityScale, realTransportVector, realTransportDiag, one_mul] using H

end Yau.Proofs.C04ChartsAux
