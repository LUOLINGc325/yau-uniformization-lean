import Yau.Proofs.C05TensorProductThirdIndices

/-! Reindexing every old slot preserves the actual covariant derivative norm. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.Proofs.C05TensorProductThirdAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L23Aux
variable {n r s q : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def liftSlots (e : Fin r ≃ Fin s) : Fin (r+1) ≃ Fin (s+1) where
  toFun i := Fin.cases 0 (fun j => (e j).succ) i
  invFun i := Fin.cases 0 (fun j => (e.symm j).succ) i
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.cases_succ,e.symm_apply_apply]
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.cases_succ,e.apply_symm_apply]

theorem covariantD_reindex_eq (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (e : Fin r ≃ Fin s) (z : ComplexVector n) :
    covariantD k c (fun w v => A w (v ∘ e)) z =
      fun v => covariantD k c A z (v ∘ liftSlots e) := by
  funext v
  have H := covariantD_reindex_cons k c A e z (v 0) (Fin.tail v)
  have hv : Fin.cons (v 0) ((Fin.tail v) ∘ e) = v ∘ liftSlots e := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  rw [hv] at H
  simpa only [Fin.cons_self_tail] using H

theorem covariantD_reindex_norm (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (e : Fin r ≃ Fin s) (z : ComplexVector n)
    (G : Matrix (RIdx n) (RIdx n) ℝ) :
    Real.sqrt (covTensorNormSq G (covariantD k c (fun w v => A w (v ∘ e)) z)) =
      Real.sqrt (covTensorNormSq G (covariantD k c A z)) := by
  rw [covariantD_reindex_eq,covTensorNormSq_reindex]

theorem covariantD_reindexed_product_norm_le (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (e : Fin (r+s) ≃ Fin q) (z : ComplexVector n)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) z) :
    Real.sqrt (covTensorNormSq G
      (covariantD k c (fun w v => tensorConcatProduct (A w) (B w) (v ∘ e)) z)) ≤
      Real.sqrt (covTensorNormSq G (covariantD k c A z)) * Real.sqrt (covTensorNormSq G (B z)) +
        Real.sqrt (covTensorNormSq G (A z)) * Real.sqrt (covTensorNormSq G (covariantD k c B z)) := by
  rw [covariantD_reindex_norm]
  exact covariantD_concatProduct_norm_le k c A B z G hG hA hB

end Yau.Proofs.C05TensorProductThirdAux
