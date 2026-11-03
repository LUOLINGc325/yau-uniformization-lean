import Yau.Proofs.E02WeightedColumns
import Yau.Proofs.E02ProductPacking
import Yau.Proofs.E02EnvelopeTestTransport

open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev ProductPoint (n m : ℕ) := ComplexVector n × ℝ × (Fin m → ComplexVector n)
abbrev ProductSpace (n m : ℕ) := ComplexVector n × (Fin m → ComplexVector n)

def weightedColumnsLinear {n m : ℕ} (α : Fin m → ℝ) :
    (Fin m → ComplexVector n) →ₗ[ℂ] Rect n m where
  toFun := weightedColumns α
  map_add' u v := by
    ext i j
    change (Real.sqrt (α j) : ℂ)*(WithLp.ofLp (u j) i+WithLp.ofLp (v j) i) = _
    exact mul_add _ _ _
  map_smul' c u := by
    ext i j
    change (Real.sqrt (α j) : ℂ)*(c*WithLp.ofLp (u j) i) =
      c*((Real.sqrt (α j) : ℂ)*WithLp.ofLp (u j) i)
    ring

def weightedColumnsCLM {n m : ℕ} (α : Fin m → ℝ) :
    (Fin m → ComplexVector n) →L[ℂ] Rect n m := (weightedColumnsLinear α).toContinuousLinearMap

def productBaseTimeCLM (n m : ℕ) : ProductPoint n m →L[ℝ] (ComplexVector n × ℝ) :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (ℝ × (Fin m → ComplexVector n))).prod
    ((ContinuousLinearMap.fst ℝ ℝ (Fin m → ComplexVector n)).comp
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ℝ × (Fin m → ComplexVector n))))

def productColumnsCLM {n m : ℕ} (α : Fin m → ℝ) : ProductPoint n m →L[ℝ] Rect n m :=
  ((weightedColumnsCLM α).restrictScalars ℝ).comp
    ((ContinuousLinearMap.snd ℝ ℝ (Fin m → ComplexVector n)).comp
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ℝ × (Fin m → ComplexVector n))))

def productSpaceSliceCLM (n m : ℕ) : ProductSpace n m →L[ℝ] ProductPoint n m :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (Fin m → ComplexVector n)).prod
    ((0 : ProductSpace n m →L[ℝ] ℝ).prod
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (Fin m → ComplexVector n)))

def productSpaceCoordinates (n m : ℕ) : ProductSpace n m →L[ℝ]
    EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) :=
  (productRealCoordinates n m).toContinuousLinearMap.comp (productSpaceSliceCLM n m)

theorem productBaseTimeCLM_apply (n m : ℕ) (Q : ProductPoint n m) :
    productBaseTimeCLM n m Q = (Q.1,Q.2.1) := rfl

theorem productColumnsCLM_apply {n m : ℕ} (α : Fin m → ℝ) (Q : ProductPoint n m) :
    productColumnsCLM α Q = weightedColumns α Q.2.2 := rfl

theorem productSpaceCoordinates_apply (n m : ℕ) (X : ComplexVector n)
    (V : Fin m → ComplexVector n) :
    productSpaceCoordinates n m (X,V) = productRealCoordinates n m (X,0,V) := rfl

theorem factorProjection_productSpace (n m : ℕ) (j : Fin m)
    (X : ComplexVector n) (V : Fin m → ComplexVector n) :
    factorProjection n m j (productSpaceCoordinates n m (X,V)) =
      envelopeSpaceCoordinates n (X,V j) := by
  rw [productSpaceCoordinates_apply,factorProjection_on_product]
  rfl

end Yau.NodeProofs.E02Aux
