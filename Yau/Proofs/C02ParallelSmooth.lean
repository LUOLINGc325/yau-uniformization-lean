import Yau.Proofs.C02ParallelChartSmooth
import Yau.Proofs.C02FlowRegularity

/-! Genuine joint smoothness of the selected complete parallel-transport
flow and its endpoint vector, on the original Whitney-sum bundle. -/

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem parallelTransportFlow_add (g : SmoothMetric M) (p : realTransportBundle M)
    (s t : ℝ) :
    realParallelTransportFlow g p (s + t) =
      realParallelTransportFlow g (realParallelTransportFlow g p s) t := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  have h := realParallelTransportFlow_unique g (realParallelTransportFlow g p s)
    (realParallelTransportFlow g p ∘ (· + s)) (by simp [realParallelTransportFlow_zero])
    ((realParallelTransportFlow_integral g p).comp_add s)
  simpa only [Function.comp_apply, add_comm] using congrFun h t

theorem parallelTransportFlow_local_finiteOrder (g : SmoothMetric M) (m : ℕ) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    LocalFlowRegularity (I := realTransportModel n) m (realParallelTransportFlow g) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  intro p
  obtain ⟨δ, hδ, hC, hball, hsol⟩ := parallelTransportChartFlow_finiteOrder g p m
  let e := extChartAt (realTransportModel n) p
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
  have hchart : ContMDiffAt (realTransportModel n)
      𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) m e q.1 :=
    contMDiffAt_extChartAt' (by simpa only [e, extChartAt_source] using hq.1.1)
  have hin : ContMDiffAt ((realTransportModel n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (ComplexVector n × (ComplexVector n × ComplexVector n)) × ℝ) m
      (fun a : realTransportBundle M × ℝ => (e a.1, a.2)) q :=
    (hchart.comp q contMDiffAt_fst).prodMk_space contMDiffAt_snd
  have hcoords' : ContDiffAt ℝ m
      (Function.uncurry (parallelTransportChartFlow g p)) (e q.1, q.2) :=
    hC.contDiffAt (hQ.mem_nhds ⟨hq.1.2, hq.2⟩)
  have hcoords : ContMDiffAt 𝓘(ℝ, (ComplexVector n × (ComplexVector n × ComplexVector n)) × ℝ)
      𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) m
      (Function.uncurry (parallelTransportChartFlow g p)) (e q.1, q.2) :=
    contMDiffAt_iff_contDiffAt.mpr hcoords'
  have hs : realParallelTransportFlow g (e.symm (e q.1)) q.2 ∈ e.source :=
    hsol (e q.1, q.2) ⟨hq.1.2, hq.2⟩
  have htarget : parallelTransportChartFlow g p (e q.1) q.2 ∈ e.target := e.map_source hs
  have hsymm : ContMDiffAt 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n))
      (realTransportModel n) m e.symm (parallelTransportChartFlow g p (e q.1) q.2) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htarget)
  have hcomp := hsymm.comp q (hcoords.comp q hin)
  have hevent : (fun a => e.symm (parallelTransportChartFlow g p (e a.1) a.2)) =ᶠ[𝓝 q]
      (fun a => realParallelTransportFlow g a.1 a.2) := by
    filter_upwards [hR.mem_nhds hq] with a ha
    have hs' := hsol (e a.1, a.2) ⟨ha.1.2, ha.2⟩
    change e.symm (e (realParallelTransportFlow g (e.symm (e a.1)) a.2)) = _
    rw [e.left_inv hs', e.left_inv ha.1.1]
  exact (hevent.contMDiffAt_iff.mp hcomp).contMDiffWithinAt

theorem parallelTransportFlow_joint_smooth (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiff ((realTransportModel n).prod 𝓘(ℝ, ℝ)) (realTransportModel n) ∞
      (fun q : realTransportBundle M × ℝ => realParallelTransportFlow g q.1 q.2) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  apply contMDiff_infty.mpr
  intro m
  exact flow_joint_contMDiff (realParallelTransportFlow_zero g) (parallelTransportFlow_add g)
    (fun p => (realParallelTransportFlow_contMDiff g p).continuous)
    (parallelTransportFlow_local_finiteOrder g m)

theorem parallelTransportEndpointVector_smooth (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    ContMDiff (realTransportModel n) (realPhaseModel n) ∞
      (fun p : realTransportBundle M =>
        realTransportVector (realParallelTransportFlow g p 1)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  have hflow := (parallelTransportFlow_joint_smooth g).comp
    (contMDiff_id.prodMk (contMDiff_const (c := (1 : ℝ))))
  exact realTransportVector_contMDiff.comp hflow

end Yau.Blueprint.C02Proof
