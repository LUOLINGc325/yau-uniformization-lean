import Yau.Proofs.P03ScalarDerivativeRows
import Yau.Proofs.P03FiniteAffinePerturbations

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Chart differentiation is linear on the actual global holomorphic
function space at every point of the genuine chart target. -/
def chartDerivativeLinearMap (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) :
    holomorphicFunctions M →ₗ[ℂ] (ComplexVector n →L[ℂ] ℂ) where
  toFun f := fderiv ℂ (inChart a (f.1 : M.Carrier → ℂ)) z
  map_add' f g := by
    have hf := ((mdifferentiable_iff_chartDifferentiable
      (f.1 : M.Carrier → ℂ)).mp f.2 a).differentiableAt
        ((isOpen_extChartAt_target a).mem_nhds hz)
    have hg := ((mdifferentiable_iff_chartDifferentiable
      (g.1 : M.Carrier → ℂ)).mp g.2 a).differentiableAt
        ((isOpen_extChartAt_target a).mem_nhds hz)
    change fderiv ℂ (fun w => inChart a (f.1 : M.Carrier → ℂ) w +
      inChart a (g.1 : M.Carrier → ℂ) w) z = _
    exact fderiv_add hf hg
  map_smul' c f := by
    have hf := ((mdifferentiable_iff_chartDifferentiable
      (f.1 : M.Carrier → ℂ)).mp f.2 a).differentiableAt
        ((isOpen_extChartAt_target a).mem_nhds hz)
    change fderiv ℂ (fun w => c • inChart a (f.1 : M.Carrier → ℂ) w) z = _
    exact fderiv_const_smul hf c

def derivativeCoordinatesLinearMap (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) : holomorphicFunctions M →ₗ[ℂ] ComplexVector n where
  toFun f := functionDerivativeCoordinates f a z
  map_add' f g := by
    ext k
    change chartDerivativeLinearMap a z hz (f + g) (stdVec k) =
      chartDerivativeLinearMap a z hz f (stdVec k) +
      chartDerivativeLinearMap a z hz g (stdVec k)
    rw [map_add]
    rfl
  map_smul' c f := by
    ext k
    change chartDerivativeLinearMap a z hz (c • f) (stdVec k) =
      c • chartDerivativeLinearMap a z hz f (stdVec k)
    rw [map_smul]
    rfl

theorem derivativeCoordinates_finiteAffinePerturbation {m L : ℕ}
    (base : Fin m → holomorphicFunctions M) (h : Fin L → holomorphicFunctions M)
    (T : Fin m → Fin L → ℂ) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) (j : Fin m) :
    functionDerivativeCoordinates (finiteAffinePerturbation base h T j) a z =
      functionDerivativeCoordinates (base j) a z +
        ∑ l, T j l • functionDerivativeCoordinates (h l) a z :=
  finiteAffinePerturbation_linearMap (derivativeCoordinatesLinearMap (M := M) a z hz)
    base h T j

end Yau.NodeProofs.P03Aux
