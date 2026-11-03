import Yau.Proofs.E02ProductContactForms
import Yau.Proofs.E02ProjectorLeviBound
import Yau.Proofs.E02VerticalContactOrder
import Yau.Proofs.E02ColumnLowerContinuity

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Every actual same-contact Peano matrix has the calculated vertical
lower bound. All projector/logdet derivatives and the constant-one trace
estimate have been supplied internally. -/
theorem sameContact_vertical_blocks (n m : ℕ)
    (u : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) → ℝ)
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (M₀ : Rect n m) (θ : ℝ)
    (Q : ProductPoint n m)
    (p : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hJet : ∀ i, RealSecondJet (u i) (factorProjection n m i (productRealCoordinates n m Q)) (p i) (A i))
    (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef)
    (hM₀ : (M₀*M₀ᴴ).PosDef) (hα : ∀ i, 0 < α i) (hθ : 0 ≤ θ)
    (slope : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) →L[ℝ] ℝ)
    (hMin : IsLocalMin (fun R => (∑ i, α i*u i (factorProjection n m i R))-
      productCostPacked f α (rowProjector M₀) θ R-slope R) (productRealCoordinates n m Q)) :
    ∀ j, ((cotangentTensor (A j)).toBlocks₂₂-columnLowerMatrix α θ Q.2.2 j).PosSemidef := by
  have hRaw := sameContact_productCost_forms n m u f α (rowProjector M₀) θ Q p A hJet hf hM slope hMin
  have hForms : ∀ (X : ComplexVector n) (V : Fin m → ComplexVector n),
      qform (leviC (fun z => f (z,Q.2.1)) Q.1) X+
        (1-θ)*rectLevi logGram (weightedColumns α Q.2.2) (weightedColumns α V) ≤
      ∑ i, α i*(star (cotangentVector X (V i)) ⬝ᵥ
        (cotangentTensor (A i)*ᵥcotangentVector X (V i))).re := by
    intro X V
    have h1 := hRaw.2 X V
    have h2 := logGram_sub_penalty_rectLevi_lower M₀ (weightedColumns α Q.2.2)
      (weightedColumns α V) hM₀ hM hθ
    unfold qform
    linarith
  intro j
  exact verticalBlock_order_of_contact_forms α Q.2.2 hα hM (fun i => cotangentTensor (A i))
    (fun i => cotangentTensor_isHermitian (A i) (hJet i).1)
    (leviC (fun z => f (z,Q.2.1)) Q.1) θ hForms j

end Yau.NodeProofs.E02Aux
