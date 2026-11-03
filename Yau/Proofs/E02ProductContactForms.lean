import Yau.Proofs.E02ProductCostTime
import Yau.Proofs.E02ProductCostLevi
import Yau.Proofs.E02SumCotangentOrder

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The actual same-Q Peano contact supplies both the original physical
time identity and the literal comparison cost's complex form inequality.
All independently chosen fiber directions use those same factor jets. -/
theorem sameContact_productCost_forms (n m : ℕ)
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
    ((∑ i, α i*p i (envelopeRealCoordinates n (0,0,1))) =
      deriv (fun t => f (Q.1,t)) Q.2.1+slope (productRealCoordinates n m (0,1,0))) ∧
    ∀ (X : ComplexVector n) (V : Fin m → ComplexVector n),
      (star (WithLp.ofLp X) ⬝ᵥ (leviC (fun z => f (z,Q.2.1)) Q.1*ᵥWithLp.ofLp X)).re+
        rectLevi logGram (weightedColumns α Q.2.2) (weightedColumns α V)-
        θ*rectLevi (projectorPenalty (n := n) P₀) (weightedColumns α Q.2.2) (weightedColumns α V) ≤
      ∑ i, α i*(star (cotangentVector X (V i)) ⬝ᵥ
        (cotangentTensor (A i)*ᵥcotangentVector X (V i))).re := by
  constructor
  · exact sumJet_productCost_time n m u f α P₀ θ Q p A hJet hf hM slope hMin
  · intro X V
    have h := sumJet_cotangent_order n m u α (productRealCoordinates n m Q) p A hJet
      (productCostPacked f α P₀ θ) (productCostPacked_contDiffAt f α P₀ θ Q hf hM)
      slope hMin X V
    rw [productCostPacked_quarter_spatial f α P₀ θ Q hf hM X V] at h
    exact h

end Yau.NodeProofs.E02Aux
