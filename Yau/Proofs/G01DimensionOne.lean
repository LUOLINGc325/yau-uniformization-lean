import Yau.Blueprint.NormalizationTargets
import Yau.LeafProofs.L12

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs

/-- Nonzero intrinsic tangent vectors in complex dimension one span their complex fiber. -/
theorem exists_smul_eq_of_dim_one {M : ComplexManifold 1} (x : M.Carrier)
    (u v : TangentVector M x) (hu : u ≠ 0) : ∃ c : ℂ, v = c • u := by
  have hcoord : tangentCoords x x u ≠ 0 := by
    intro hz
    apply hu
    have he := L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x) u
    rw [hz] at he
    exact he.symm.trans ((mfderiv (ComplexModel 1) (ComplexModel 1)
      (extChartAt (ComplexModel 1) x).symm (chartPt x x)).map_zero)
  have hzero : tangentCoords x x u 0 ≠ 0 := by
    intro hz
    apply hcoord
    ext i
    fin_cases i
    exact hz
  let c := tangentCoords x x v 0 / tangentCoords x x u 0
  have hv : tangentCoords x x v = c • tangentCoords x x u := by
    ext i
    fin_cases i
    change tangentCoords x x v 0 = c * tangentCoords x x u 0
    exact (div_mul_cancel₀ _ hzero).symm
  refine ⟨c, ?_⟩
  calc
    v = chartVec x x (tangentCoords x x v) :=
      (L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x) v).symm
    _ = c • u := by
      rw [hv, L12Aux.chartVec_complex_smul,
        L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x) u]

end Yau.NodeProofs.G01Aux
