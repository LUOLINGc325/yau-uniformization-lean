import Yau.Proofs.F01LargestRayleighContinuity
import Yau.Proofs.F01FamilyChartGram
import Yau.Proofs.F01RayleighChartInvariant

/-! The largest relative metric eigenvalue is genuinely continuous in
each fixed holomorphic chart, on the full original closed time set. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamily_largestRayleigh_continuousOn_chart
    (g k : ℝ → HermitianField M) {I : Set ℝ}
    (hg : MetricFamilySmooth g I) (hk : MetricFamilySmooth k I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target) :
    ContinuousOn (fun p : ComplexVector n × ℝ =>
      metricLargestRayleigh (g p.2) (k p.2) (e p.1)) (e.source ×ˢ I) := by
  have hG : ContinuousOn (fun p : ComplexVector n × ℝ =>
      fun i j => pullbackMatrix (g p.2) e p.1 i j) (e.source ×ˢ I) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (metricFamily_pullback_contDiffOn g hg e he i j).continuousOn
  have hH : ContinuousOn (fun p : ComplexVector n × ℝ =>
      fun i j => pullbackMatrix (k p.2) e p.1 i j) (e.source ×ˢ I) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (metricFamily_pullback_contDiffOn k hk e he i j).continuousOn
  have hRayleigh := largestMatrixRayleigh_continuousOn
    (fun p : ComplexVector n × ℝ => pullbackMatrix (g p.2) e p.1)
    (fun p : ComplexVector n × ℝ => pullbackMatrix (k p.2) e p.1)
    hG hH (fun p hp => pullbackMatrix_posDef (g p.2) e he hei hp.1)
    (fun p hp => pullbackMatrix_posDef (k p.2) e he hei hp.1)
  apply hRayleigh.congr
  intro p hp
  exact (largestRayleigh_pullback_eq (g p.2) (k p.2) e he hei hp.1).symm

end Yau.NodeProofs.F01Aux
