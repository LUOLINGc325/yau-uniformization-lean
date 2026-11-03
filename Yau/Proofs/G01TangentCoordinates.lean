import Yau.Proofs.G01Calculator

noncomputable section
open scoped Manifold
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem tangentCoords_ne_zero_iff (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : TangentVector M y) :
    tangentCoords x y v ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro hc hv
    apply hc
    rw [hv]
    exact (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x) y).map_zero
  · intro hv hc
    apply hv
    have he := L12Aux.chartVec_tangentCoords x y hy v
    rw [hc] at he
    exact he.symm.trans ((mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x).symm (chartPt x y)).map_zero)

theorem chartVec_ne_zero_iff (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : ComplexVector n) :
    chartVec x y v ≠ 0 ↔ v ≠ 0 := by
  have hz : chartVec x y (0 : ComplexVector n) = 0 :=
    (mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x).symm (chartPt x y)).map_zero
  constructor
  · intro hv hc
    exact hv (hc ▸ hz)
  · intro hv hc
    exact hv ((L12Aux.chartVec_injective x y hy) (hc.trans hz.symm))

theorem tangentCoordinates_ne_zero_iff (x : M.Carrier) (v : TangentVector M x) :
    tangentCoordinates x v ≠ 0 ↔ v ≠ 0 :=
  tangentCoords_ne_zero_iff x x (mem_extChartAt_source x) v

end Yau.NodeProofs.G01Aux
