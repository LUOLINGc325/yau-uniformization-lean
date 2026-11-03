import Yau.Proofs.V03Coordinates

/-! The induced Gram left inverse turns the actual coordinate Hessian
into an ambient tensor. Its frame contraction is exact, and its definition
is invariant under every invertible coordinate change, including rank zero. -/

open scoped Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def gramLeftInverse (A : Matrix κ ι ℂ) : Matrix ι κ ℂ := (Aᴴ * A)⁻¹ * Aᴴ

def ambientLeviTensor (A : Matrix κ ι ℂ) (H : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  (gramLeftInverse A)ᴴ * H * gramLeftInverse A

theorem gramLeftInverse_mul {A : Matrix κ ι ℂ} (hA : IsUnit (Aᴴ * A)) :
    gramLeftInverse A * A = 1 := by
  unfold gramLeftInverse
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)

theorem ambientLeviTensor_frame {A : Matrix κ ι ℂ} (hA : IsUnit (Aᴴ * A))
    (H E : Matrix ι ι ℂ) :
    (A * E)ᴴ * ambientLeviTensor A H * (A * E) = Eᴴ * H * E := by
  have hJE : gramLeftInverse A * (A * E) = E := by
    rw [← Matrix.mul_assoc, gramLeftInverse_mul hA, Matrix.one_mul]
  calc
    _ = (gramLeftInverse A * (A * E))ᴴ * H * (gramLeftInverse A * (A * E)) := by
      simp only [ambientLeviTensor, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hJE]

theorem gramLeftInverse_right_mul (A : Matrix κ ι ℂ) (S : Matrix ι ι ℂ) (hS : IsUnit S) :
    gramLeftInverse (A * S) = S⁻¹ * gramLeftInverse A := by
  have hSd := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hSHd : IsUnit Sᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hSd.star
  have hGram : (A * S)ᴴ * (A * S) = Sᴴ * (Aᴴ * A) * S := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold gramLeftInverse
  rw [hGram, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_inv_rev]
  calc
    S⁻¹ * ((Aᴴ * A)⁻¹ * (Sᴴ)⁻¹) * (Sᴴ * Aᴴ) =
        S⁻¹ * (Aᴴ * A)⁻¹ * ((Sᴴ)⁻¹ * Sᴴ) * Aᴴ := by simp only [Matrix.mul_assoc]
    _ = S⁻¹ * ((Aᴴ * A)⁻¹ * Aᴴ) := by
      rw [Matrix.nonsing_inv_mul _ hSHd, Matrix.mul_one, Matrix.mul_assoc]

theorem ambientLeviTensor_covariant (A : Matrix κ ι ℂ) (H S : Matrix ι ι ℂ)
    (hS : IsUnit S) :
    ambientLeviTensor (A * S) (Sᴴ * H * S) = ambientLeviTensor A H := by
  have hSJ : S * gramLeftInverse (A * S) = gramLeftInverse A := by
    rw [gramLeftInverse_right_mul A S hS, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS), Matrix.one_mul]
  calc
    _ = (S * gramLeftInverse (A * S))ᴴ * H * (S * gramLeftInverse (A * S)) := by
      simp only [ambientLeviTensor, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hSJ]; rfl

end Yau.Blueprint.V03Proof
