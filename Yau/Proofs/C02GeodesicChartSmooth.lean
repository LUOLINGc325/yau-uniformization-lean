import Yau.Proofs.C02ODESmooth
import Yau.LeafProofs.L12GeodesicVariation

/-! Every finite order holds for the actual chosen geodesic flow in fixed
coordinates. The coordinate neighborhood may depend on the finite order. -/

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realGeodesicChartFlow_finiteOrder (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (m : ℕ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ δ > (0 : ℝ),
      ContDiffOn ℝ m (Function.uncurry (realGeodesicChartFlow g p))
        (Metric.ball (extChartAt (realPhaseModel n) p p) δ ×ˢ Ioo (-δ) δ) ∧
      Metric.ball (extChartAt (realPhaseModel n) p p) δ ⊆
        (extChartAt (realPhaseModel n) p).target ∧
      ∀ q ∈ Metric.ball (extChartAt (realPhaseModel n) p p) δ ×ˢ Ioo (-δ) δ,
        realGeodesicFlow g ((extChartAt (realPhaseModel n) p).symm q.1) q.2 ∈
          (extChartAt (realPhaseModel n) p).source := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhase_t2Space M
  letI := realPhaseModel_boundaryless n
  let e := extChartAt (realPhaseModel n) p
  have hz₀ : e p ∈ chartTarget p.proj ×ˢ (univ : Set (ComplexVector n)) :=
    ⟨(realPhaseChart_target p _).mp (mem_extChartAt_target p), mem_univ _⟩
  have hO : IsOpen (chartTarget p.proj ×ˢ (univ : Set (ComplexVector n))) :=
    (isOpen_extChartAt_target (I := ComplexModel n) p.proj).prod isOpen_univ
  have hF : ContDiffAt ℝ ∞ (chartGeodesicSpray g.form p.proj) (e p) :=
    (chartGeodesicSpray_contDiffOn g p.proj).contDiffAt (hO.mem_nhds hz₀)
  obtain ⟨d⟩ := exists_localVariationalFlow (hF.of_le (by simp))
    (isOpen_extChartAt_target (I := realPhaseModel n) p) (mem_extChartAt_target p)
  have hzero : (0 : ℝ) ∈ Ioo (-d.duration) d.duration :=
    ⟨by linarith [d.duration_pos], d.duration_pos⟩
  have hG := (realGeodesicSpray_contMDiff g).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have heq : ∀ z ∈ Metric.ball (e p) d.radius, ∀ t ∈ Ioo (-d.duration) d.duration,
      e.symm (d.solution z t) = realGeodesicFlow g (e.symm z) t := by
    intro z hz
    have hη : ∀ t ∈ Ioo (-d.duration) d.duration,
        (d.solution z t).1 ∈ chartTarget p.proj ∧
          HasDerivAt (d.solution z) (chartGeodesicSpray g.form p.proj (d.solution z t)) t := by
      intro t ht
      exact ⟨(realPhaseChart_target p _).mp (d.equation z hz t ht).1,
        (d.equation z hz t ht).2.1⟩
    have hγ := chartGeodesic_phase_isMIntegralCurveOn g p (d.solution z) hη
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero hG hγ
      ((realGeodesicFlow_integral g (e.symm z)).isMIntegralCurveOn _)
      (by rw [(d.initial z hz).1, realGeodesicFlow_zero])
  have hcoords : ∀ q ∈ d.domain,
      realGeodesicChartFlow g p q.1 q.2 = d.solution q.1 q.2 := by
    intro q hq
    unfold realGeodesicChartFlow
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
