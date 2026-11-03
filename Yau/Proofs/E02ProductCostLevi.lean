import Yau.Proofs.E02ProductCostHessian
import Yau.Proofs.E02BaseLeviQuadratic

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The literal packed comparison cost has exactly the original
spatial Levi plus the calculated rectangular logdet and projector terms. -/
theorem productCostPacked_quarter_spatial {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q : ProductPoint n m)
    (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef)
    (X : ComplexVector n) (V : Fin m → ComplexVector n) :
    (fderiv ℝ (fderiv ℝ (productCostPacked f α P₀ θ)) (productRealCoordinates n m Q)
        (productSpaceCoordinates n m (X,V)) (productSpaceCoordinates n m (X,V))+
      fderiv ℝ (fderiv ℝ (productCostPacked f α P₀ θ)) (productRealCoordinates n m Q)
        (productSpaceCoordinates n m (Complex.I • X,fun i => Complex.I • V i))
        (productSpaceCoordinates n m (Complex.I • X,fun i => Complex.I • V i)))/4 =
      (star (WithLp.ofLp X) ⬝ᵥ (leviC (fun z => f (z,Q.2.1)) Q.1*ᵥWithLp.ofLp X)).re+
        rectLevi logGram (weightedColumns α Q.2.2) (weightedColumns α V)-
        θ*rectLevi (projectorPenalty (n := n) P₀) (weightedColumns α Q.2.2) (weightedColumns α V) := by
  have hI : weightedColumns α (fun i => Complex.I • V i) = Complex.I • weightedColumns α V :=
    (weightedColumnsLinear α).map_smul Complex.I V
  let U : ProductPoint n m := (X,0,V)
  let W : ProductPoint n m := (Complex.I • X,0,fun i => Complex.I • V i)
  have h1 := (productCostPacked_second_apply f α P₀ θ Q U U hf hM).trans
    (productCostPhysical_second_apply f α P₀ θ Q U U hf hM)
  have h2 := (productCostPacked_second_apply f α P₀ θ Q W W hf hM).trans
    (productCostPhysical_second_apply f α P₀ θ Q W W hf hM)
  change (fderiv ℝ (fderiv ℝ (productCostPacked f α P₀ θ)) (productRealCoordinates n m Q)
      (productRealCoordinates n m U) (productRealCoordinates n m U)+
    fderiv ℝ (fderiv ℝ (productCostPacked f α P₀ θ)) (productRealCoordinates n m Q)
      (productRealCoordinates n m W) (productRealCoordinates n m W))/4 = _
  rw [h1,h2,baseTime_leviC_quadratic hf X]
  dsimp only [U,W]
  rw [hI]
  unfold rectLevi
  ring

end Yau.NodeProofs.E02Aux
