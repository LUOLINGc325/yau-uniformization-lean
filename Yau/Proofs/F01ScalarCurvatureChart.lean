import Yau.Proofs.F01HeatChartNaturality
import Yau.LeafProofs.L17RicciNaturality

/-! The original computed scalar curvature equals the actual chart
inverse-metric trace of the chart Ricci matrix. -/
noncomputable section
open scoped Manifold Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarCurvature_holomorphic_chart (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    traceWith (pullbackMatrix g e z) (pullbackRicci g e z) = scalarCurvature g (e z) := by
  rw [pullbackMatrix_eq_congruence g e (e z) z (mem_extChartAt_source (e z)),
    pullbackRicci_eq_ricci g hg e he hei hz]
  exact traceWith_congruence _ _ _ (linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e he hei (e z) hz (mem_extChartAt_source (e z))))

end Yau.NodeProofs.F01Aux
