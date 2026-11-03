import Yau.Proofs.C02GeodesicChartSmooth
import Yau.Proofs.C02FlowRegularity

/-! Joint infinite regularity of the actual complete geodesic flow. Each
finite order is propagated along the existing compact trajectory, then the
finite-order characterization is applied to this one globally defined map. -/

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realGeodesicFlow_local_finiteOrder (g : SmoothMetric M) (m : ℕ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    LocalFlowRegularity (I := realPhaseModel n) m (realGeodesicFlow g) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  intro p
  obtain ⟨δ, hδ, hC, hball, hsol⟩ := realGeodesicChartFlow_finiteOrder g p m
  let e := extChartAt (realPhaseModel n) p
  let U := e.source ∩ e ⁻¹' Metric.ball (e p) δ
  have hU : IsOpen U :=
    (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p)
      Metric.isOpen_ball
  have hpU : p ∈ U := ⟨mem_extChartAt_source p, Metric.mem_ball_self hδ⟩
  have hQ : IsOpen (Metric.ball (e p) δ ×ˢ Ioo (-δ) δ) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hR : IsOpen (U ×ˢ Ioo (-δ) δ) := hU.prod isOpen_Ioo
  refine ⟨U, hU, hpU, δ, hδ, ?_⟩
  intro q hq
  have hchart : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n)
      m e q.1 :=
    contMDiffAt_extChartAt' (by simpa only [e, extChartAt_source] using hq.1.1)
  have hin : ContMDiffAt ((realPhaseModel n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (ComplexVector n × ComplexVector n) × ℝ) m
      (fun a : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        (e a.1, a.2)) q :=
    (hchart.comp q contMDiffAt_fst).prodMk_space contMDiffAt_snd
  have hcoords' : ContDiffAt ℝ m
      (Function.uncurry (realGeodesicChartFlow g p)) (e q.1, q.2) :=
    hC.contDiffAt (hQ.mem_nhds ⟨hq.1.2, hq.2⟩)
  have hcoords : ContMDiffAt 𝓘(ℝ, (ComplexVector n × ComplexVector n) × ℝ)
      𝓘(ℝ, ComplexVector n × ComplexVector n) m
      (Function.uncurry (realGeodesicChartFlow g p)) (e q.1, q.2) :=
    contMDiffAt_iff_contDiffAt.mpr hcoords'
  have hs : realGeodesicFlow g (e.symm (e q.1)) q.2 ∈ e.source :=
    hsol (e q.1, q.2) ⟨hq.1.2, hq.2⟩
  have htarget : realGeodesicChartFlow g p (e q.1) q.2 ∈ e.target := e.map_source hs
  have hsymm : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n)
      (realPhaseModel n) m e.symm (realGeodesicChartFlow g p (e q.1) q.2) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htarget)
  have hcomp := hsymm.comp q (hcoords.comp q hin)
  have hevent : (fun a => e.symm (realGeodesicChartFlow g p (e a.1) a.2)) =ᶠ[𝓝 q]
      (fun a => realGeodesicFlow g a.1 a.2) := by
    filter_upwards [hR.mem_nhds hq] with a ha
    have hs' := hsol (e a.1, a.2) ⟨ha.1.2, ha.2⟩
    change e.symm (e (realGeodesicFlow g (e.symm (e a.1)) a.2)) = _
    rw [e.left_inv hs', e.left_inv ha.1.1]
  exact (hevent.contMDiffAt_iff.mp hcomp).contMDiffWithinAt

theorem realGeodesicFlow_joint_smooth (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) (realPhaseModel n) ∞
      (fun q : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        realGeodesicFlow g q.1 q.2) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  apply contMDiff_infty.mpr
  intro m
  exact flow_joint_contMDiff (realGeodesicFlow_zero g) (realGeodesicFlow_add g)
    (fun p => (realGeodesicFlow_contMDiff g p).continuous)
    (realGeodesicFlow_local_finiteOrder g m)

theorem realExponentialBundle_smooth (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n) 𝓘(ℝ, ComplexVector n) ∞
      (fun p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
        (realGeodesicFlow g p 1).proj) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have hflow := (realGeodesicFlow_joint_smooth g).comp
    (contMDiff_id.prodMk (contMDiff_const (c := (1 : ℝ))))
  exact (Bundle.contMDiff_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := ∞)
    (TangentSpace 𝓘(ℝ, ComplexVector n))).comp hflow

theorem realExponentialMap_smooth (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n) ∞
      (realExponentialMap g x) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  exact (realExponentialBundle_smooth g).comp (realTangentFiber_contMDiff g x)

end Yau.Blueprint.C02Proof
