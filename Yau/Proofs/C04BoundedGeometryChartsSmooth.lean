import Yau.Proofs.C04BoundedGeometryChartsGeodesicRegularity

/-! Smoothness of the same chosen complete flow and exponential. -/

noncomputable section
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realGeodesicFlow_joint_smooth (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff ((realPhaseModel n).prod 𝓘(ℝ, ℝ)) (realPhaseModel n) ∞
      (fun q : (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) × ℝ =>
        realGeodesicFlow g q.1 q.2) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro p
  exact contMDiffAt_iff_nat.mpr fun m _ => realGeodesicFlow_joint_contMDiff_order m g p

theorem realExponentialBundle_smooth (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n) 𝓘(ℝ, ComplexVector n) ∞
      (fun p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
        (realGeodesicFlow g p 1).proj) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro p
  exact contMDiffAt_iff_nat.mpr fun m _ => realExponentialBundle_contMDiff_order m g p

theorem realExponentialMap_smooth (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n) ∞
      (realExponentialMap g x) := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  intro v
  exact contMDiffAt_iff_nat.mpr fun m _ => realExponentialMap_contMDiff_order m g x v

end Yau.Proofs.C04ChartsAux
