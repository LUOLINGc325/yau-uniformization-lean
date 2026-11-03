import Yau.Proofs.C02ODESmooth
import Yau.Proofs.C02ChartIntegralCurve
import Yau.LeafProofs.L12ParallelTransport

/-! Finite-order initial-data dependence of the actual complete parallel
transport flow, obtained from the same coordinate ODE and uniqueness. -/

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def parallelTransportChartFlow (g : SmoothMetric M) (p : realTransportBundle M)
    (z : ComplexVector n × (ComplexVector n × ComplexVector n)) (t : ℝ) :
    ComplexVector n × (ComplexVector n × ComplexVector n) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  exact extChartAt (realTransportModel n) p
    (realParallelTransportFlow g ((extChartAt (realTransportModel n) p).symm z) t)

theorem parallelTransportChartFlow_finiteOrder (g : SmoothMetric M)
    (p : realTransportBundle M) (m : ℕ) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ∃ δ > (0 : ℝ),
      ContDiffOn ℝ m (Function.uncurry (parallelTransportChartFlow g p))
        (Metric.ball (extChartAt (realTransportModel n) p p) δ ×ˢ Ioo (-δ) δ) ∧
      Metric.ball (extChartAt (realTransportModel n) p p) δ ⊆
        (extChartAt (realTransportModel n) p).target ∧
      ∀ q ∈ Metric.ball (extChartAt (realTransportModel n) p p) δ ×ˢ Ioo (-δ) δ,
        realParallelTransportFlow g ((extChartAt (realTransportModel n) p).symm q.1) q.2 ∈
          (extChartAt (realTransportModel n) p).source := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransport_t2Space M
  letI := realTransportModel_boundaryless n
  let e := extChartAt (realTransportModel n) p
  have hz₀ : e p ∈ chartTarget p.proj ×ˢ
      (univ : Set (ComplexVector n × ComplexVector n)) :=
    ⟨(realTransportChart_target p _).mp (mem_extChartAt_target p), mem_univ _⟩
  have hO : IsOpen (chartTarget p.proj ×ˢ
      (univ : Set (ComplexVector n × ComplexVector n))) :=
    (isOpen_extChartAt_target (I := ComplexModel n) p.proj).prod isOpen_univ
  have hF : ContDiffAt ℝ ∞ (chartParallelTransportField g.form p.proj) (e p) :=
    (chartParallelTransportField_contDiffOn g p.proj).contDiffAt (hO.mem_nhds hz₀)
  obtain ⟨d⟩ := exists_localVariationalFlow (hF.of_le (by simp))
    (isOpen_extChartAt_target (I := realTransportModel n) p) (mem_extChartAt_target p)
  have hzero : (0 : ℝ) ∈ Ioo (-d.duration) d.duration :=
    ⟨by linarith [d.duration_pos], d.duration_pos⟩
  have hG := (realParallelTransportSpray_contMDiff g).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have heq : ∀ z ∈ Metric.ball (e p) d.radius, ∀ t ∈ Ioo (-d.duration) d.duration,
      e.symm (d.solution z t) = realParallelTransportFlow g (e.symm z) t := by
    intro z hz
    have hγ := chart_ODE_isMIntegralCurveOn (I := realTransportModel n) p
      (chartParallelTransportField g.form p.proj) (realParallelTransportSpray g)
      (d.solution z) (tangentCoordChange_realParallelTransportSpray g p)
      (fun t ht => ⟨(d.equation z hz t ht).1, (d.equation z hz t ht).2.1⟩)
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero hG hγ
      ((realParallelTransportFlow_integral g (e.symm z)).isMIntegralCurveOn _)
      (by rw [(d.initial z hz).1, realParallelTransportFlow_zero])
  have hcoords : ∀ q ∈ d.domain,
      parallelTransportChartFlow g p q.1 q.2 = d.solution q.1 q.2 := by
    intro q hq
    unfold parallelTransportChartFlow
    rw [← heq q.1 hq.1 q.2 hq.2]
    exact e.right_inv (d.equation q.1 hq.1 q.2 hq.2).1
  obtain ⟨δ, hδ, hsub, hreg⟩ := d.exists_finiteOrder_rectangle hF m
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · exact (contDiffOn_congr (fun q hq => hcoords q (hsub hq))).mpr hreg
  · intro z hz
    have hmem := hsub (show (z, 0) ∈ Metric.ball (e p) δ ×ˢ Ioo (-δ) δ from
      ⟨hz, by constructor <;> linarith⟩)
    have htarg := (d.equation z hmem.1 0 hmem.2).1
    rwa [(d.initial z hmem.1).1] at htarg
  · intro q hq
    have hmem := hsub hq
    rw [← heq q.1 hmem.1 q.2 hmem.2]
    exact e.map_target (d.equation q.1 hmem.1 q.2 hmem.2).1

end Yau.Blueprint.C02Proof
