import Yau.Proofs.D05CanonicalAlgebra
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The Hamiltonian columns span by the actual algebraic transpose-duality
surjectivity theorem in Mathlib. No regular right inverse is selected. -/

noncomputable section
open Matrix
open scoped Matrix
namespace Yau.Blueprint.V01Proof

theorem canonical_columns_span_of_injective {n q : ℕ}
    (A : Matrix (Fin q) (CotangentIndex n) ℂ) (hA : Function.Injective A.mulVec) :
    Submodule.span ℂ (Set.range (fun j : Fin q =>
      (fun i => ((canonicalBivector : CotangentMatrix n) * Aᵀ) i j))) = ⊤ := by
  have hAt : Function.Surjective Aᵀ.mulVec := by
    intro v
    obtain ⟨u, hu⟩ := (Matrix.mulVec_injective_iff.mp hA).vecMul_surjective v
    exact ⟨u, (Matrix.mulVec_transpose A u).trans hu⟩
  have hJ : Function.Surjective (canonicalBivector : CotangentMatrix n).mulVec := by
    intro v
    refine ⟨-(canonicalBivector *ᵥ v), ?_⟩
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Yau.Blueprint.D05Proof.canonicalBivector_square,
      Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
  have hJA : Function.Surjective ((canonicalBivector : CotangentMatrix n) * Aᵀ).mulVec := by
    intro v
    obtain ⟨w, hw⟩ := hJ v
    obtain ⟨u, hu⟩ := hAt w
    refine ⟨u, ?_⟩
    rw [← Matrix.mulVec_mulVec, hu, hw]
  change Submodule.span ℂ
    (Set.range ((canonicalBivector : CotangentMatrix n) * Aᵀ).col) = ⊤
  exact (Matrix.range_mulVecLin ((canonicalBivector : CotangentMatrix n) * Aᵀ)).symm.trans
      (LinearMap.range_eq_top.mpr hJA)

end Yau.Blueprint.V01Proof
