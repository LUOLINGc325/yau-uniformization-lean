import Yau.Proofs.V03AmbientTensorAlgebra

/-! Exact native quadratic contraction and complex scalar homogeneity
for the actual Gram-transported Levi tensor. -/

open scoped Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem ambientLeviTensor_vectors {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A : Matrix κ ι ℂ} (hA : IsUnit (Aᴴ * A)) (H : Matrix ι ι ℂ) (u v : ι → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (ambientLeviTensor A H *ᵥ (A *ᵥ v)) = star u ⬝ᵥ (H *ᵥ v) := by
  have hm : Aᴴ * ambientLeviTensor A H * A = H := by
    simpa only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one] using
      ambientLeviTensor_frame hA H 1
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hm]

theorem quadratic_complex_smul {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (v : ι → ℂ) (c : ℂ) :
    star (c • v) ⬝ᵥ (H *ᵥ (c • v)) = star c * c * (star v ⬝ᵥ (H *ᵥ v)) := by
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

end Yau.Blueprint.V03Proof
