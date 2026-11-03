import Yau.Proofs.E02ProductCost
import Yau.Proofs.E02SumJetMinimum

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem productCostPacked_time_fderiv {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q : ProductPoint n m)
    (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef) :
    fderiv ℝ (productCostPacked f α P₀ θ) (productRealCoordinates n m Q)
      (productRealCoordinates n m (0,1,0)) = deriv (fun t => f (Q.1,t)) Q.2.1 := by
  have hTime : HasDerivAt (fun t : ℝ => (Q.1,t,Q.2.2)) (0,1,0) Q.2.1 := by
    simpa using (hasDerivAt_const Q.2.1 Q.1).prodMk
      ((hasDerivAt_id Q.2.1).prodMk (hasDerivAt_const Q.2.1 Q.2.2))
  have hPacked := (productRealCoordinates n m).hasFDerivAt.comp_hasDerivAt Q.2.1 hTime
  have hCost := (productCostPacked_contDiffAt f α P₀ θ Q hf hM).differentiableAt (by simp)
  have hValue := (hCost.hasFDerivAt.comp_hasDerivAt Q.2.1 hPacked).deriv
  have hFun : (fun t => productCostPacked f α P₀ θ (productRealCoordinates n m (Q.1,t,Q.2.2))) =
      (fun t => productCostPhysical f α P₀ θ (Q.1,t,Q.2.2)) := by
    funext t
    simp only [productCostPacked,ContinuousLinearEquiv.symm_apply_apply]
  simp only [Function.comp_def] at hValue
  rw [hFun,productCostPhysical_time_deriv] at hValue
  exact hValue.symm

/-- The physical time equation uses the original ONE shared time
direction in the product and every factor projection. -/
theorem sumJet_productCost_time (n m : ℕ)
    (u : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) → ℝ)
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ)
    (Q : ProductPoint n m)
    (p : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hJet : ∀ i, RealSecondJet (u i) (factorProjection n m i (productRealCoordinates n m Q)) (p i) (A i))
    (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef)
    (slope : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) →L[ℝ] ℝ)
    (hMin : IsLocalMin (fun R => (∑ i, α i*u i (factorProjection n m i R))-
      productCostPacked f α P₀ θ R-slope R) (productRealCoordinates n m Q)) :
    (∑ i, α i*p i (envelopeRealCoordinates n (0,0,1))) =
      deriv (fun t => f (Q.1,t)) Q.2.1+slope (productRealCoordinates n m (0,1,0)) := by
  have hC := productCostPacked_contDiffAt f α P₀ θ Q hf hM
  have hTime := (sumJet_localMin_constraints (factorProjection n m) u α
    (productRealCoordinates n m Q) p A hJet (productCostPacked f α P₀ θ) _ _
    (realSecondJet_of_contDiffAt_two hC) slope hMin).1 (productRealCoordinates n m (0,1,0))
  simpa only [factorProjection_on_product,Pi.zero_apply,productCostPacked_time_fderiv f α P₀ θ Q hf hM] using hTime

end Yau.NodeProofs.E02Aux
