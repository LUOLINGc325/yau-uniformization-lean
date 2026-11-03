import Yau.Proofs.V03AmbientTensorAlgebra

/-! Exact vector contractions of the actual immersion Gram tensor;
the identities retain rank zero and need no choice of a frame column. -/

open scoped Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem ambientLeviTensor_vector {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A : Matrix κ ι ℂ} (hA : IsUnit (Aᴴ * A)) (H : Matrix ι ι ℂ) (v : ι → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (ambientLeviTensor A H *ᵥ (A *ᵥ v)) = star v ⬝ᵥ (H *ᵥ v) := by
  have hJ : gramLeftInverse A *ᵥ (A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, gramLeftInverse_mul hA, Matrix.one_mulVec]
  calc
    _ = star (gramLeftInverse A *ᵥ (A *ᵥ v)) ⬝ᵥ
        (H *ᵥ (gramLeftInverse A *ᵥ (A *ᵥ v))) := by
      conv_rhs => rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
      simp only [ambientLeviTensor, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [hJ]

end Yau.Blueprint.V03Proof
