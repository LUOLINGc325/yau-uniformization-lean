import Yau.Proofs.F01LargestRayleigh
import Yau.LeafProofs.L17ChartNaturality

/-! The largest relative eigenvalue is independent of the actual holomorphic
chart. This avoids continuity claims about the center-dependent native frame. -/
noncomputable section
open scoped Manifold Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def metricLargestRayleigh (g k : HermitianField M) (p : M.Carrier) : ℝ :=
  largestMatrixRayleigh (gMat g p) (gMat k p)

theorem largestRayleigh_pullback_eq (g k : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    largestMatrixRayleigh (pullbackMatrix g e z) (pullbackMatrix k e z) =
      metricLargestRayleigh g k (e z) := by
  let a := e z
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hJ : IsUnit (linearMatrix (coordinateDifferential e a z)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero _
        (coordinateDifferential_injective e he hei a hz ha)))
  rw [pullbackMatrix_eq_congruence g e a z ha, pullbackMatrix_eq_congruence k e a z ha]
  exact largestMatrixRayleigh_congruence _ _ _ hJ

theorem fixed_chart_rayleigh_le_largest (g k : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (v : Fin n → ℂ) :
    matrixRayleigh (pullbackMatrix g e z) (pullbackMatrix k e z) v ≤
      metricLargestRayleigh g k (e z) := by
  rw [← largestRayleigh_pullback_eq g k e he hei hz]
  exact matrixRayleigh_le_largest (pullbackMatrix_posDef g e he hei hz)
    (pullbackMatrix_posDef k e he hei hz) v

end Yau.NodeProofs.F01Aux
