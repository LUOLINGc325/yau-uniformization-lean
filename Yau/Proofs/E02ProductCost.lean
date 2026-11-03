import Yau.Proofs.E02ProductMaps
import Yau.Proofs.E02RectangularLevi
import Yau.Proofs.E02LeviLinear

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The actual comparison function on the physical product with one
base and one time; the weighted rectangular matrix retains every fiber. -/
def productCostPhysical {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q : ProductPoint n m) : ℝ :=
  (n : ℝ)+f (Q.1,Q.2.1)+logGram (weightedColumns α Q.2.2)-
    θ*projectorPenalty (n := n) P₀ (weightedColumns α Q.2.2)

theorem projectorPenalty_contDiffAt {n m : ℕ} (P₀ : Herm m) (M : Rect n m)
    (hM : (M*Mᴴ).PosDef) : ContDiffAt ℝ ∞ (projectorPenalty (n := n) P₀) M := by
  have h := (rowProjector_contDiffAt M hM).continuousLinearMap_comp (projectorTraceCLM P₀)
  exact contDiffAt_const.sub h

theorem productCostPhysical_contDiffAt {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q : ProductPoint n m)
    (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef) :
    ContDiffAt ℝ 2 (productCostPhysical f α P₀ θ) Q := by
  have hBase := hf.comp Q (productBaseTimeCLM n m).contDiff.contDiffAt
  have hLog : ContDiffAt ℝ 2 logGram (productColumnsCLM α Q) :=
    ((logGram_contDiffOn n m).contDiffAt ((isOpen_fullRankRect n m).mem_nhds
      ((fullRankRect_iff_posDef _).mpr hM))).of_le (by simp)
  have hLogComp := hLog.comp Q (productColumnsCLM α).contDiff.contDiffAt
  have hPenaltyAt : ContDiffAt ℝ 2 (projectorPenalty (n := n) P₀) (productColumnsCLM α Q) :=
    (projectorPenalty_contDiffAt P₀ _ hM).of_le (by simp)
  have hPenalty := hPenaltyAt.comp Q (productColumnsCLM α).contDiff.contDiffAt
  exact ((contDiffAt_const.add hBase).add hLogComp).sub (contDiffAt_const.mul hPenalty)

theorem productCostPhysical_time_deriv {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q : ProductPoint n m) :
    deriv (fun t => productCostPhysical f α P₀ θ (Q.1,t,Q.2.2)) Q.2.1 =
      deriv (fun t => f (Q.1,t)) Q.2.1 := by
  unfold productCostPhysical
  change deriv (fun t => (n : ℝ)+f (Q.1,t)+logGram (weightedColumns α Q.2.2)-
    θ*projectorPenalty (n := n) P₀ (weightedColumns α Q.2.2)) Q.2.1 = _
  rw [deriv_sub_const,deriv_add_const,deriv_const_add]

def productCostPacked {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ)
    (q : EuclideanSpace ℝ (Fin (2*n+1+2*n*m))) : ℝ :=
  productCostPhysical f α P₀ θ ((productRealCoordinates n m).symm q)

theorem productCostPacked_contDiffAt {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q : ProductPoint n m)
    (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef) :
    ContDiffAt ℝ 2 (productCostPacked f α P₀ θ) (productRealCoordinates n m Q) := by
  have hCost := productCostPhysical_contDiffAt f α P₀ θ Q hf hM
  have hAt : ContDiffAt ℝ 2 (productCostPhysical f α P₀ θ)
      ((productRealCoordinates n m).symm (productRealCoordinates n m Q)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hCost
  exact hAt.comp _ (productRealCoordinates n m).symm.contDiff.contDiffAt

end Yau.NodeProofs.E02Aux
