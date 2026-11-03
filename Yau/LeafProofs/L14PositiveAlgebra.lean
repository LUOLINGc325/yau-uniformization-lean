import Yau.LeafProofs.L14
import Yau.LeafProofs.L14CurvatureAlgebra

noncomputable section
open scoped Matrix
namespace Yau.LeafProofs.L14Aux

theorem positiveTrace_coordinate_change {n : ℕ}
    (G J U V : Matrix (Fin n) (Fin n) ℂ) (hJ : IsUnit J.det) :
    ((Jᴴ * U * (J⁻¹)ᵀ)ᴴ * (Jᴴ * G * J)⁻¹ * (Jᴴ * V * (J⁻¹)ᵀ) * (Jᴴ * G * J)ᵀ).trace =
      (Uᴴ * G⁻¹ * V * Gᵀ).trace := by
  let B := (J⁻¹)ᵀ
  have hJH : IsUnit (Jᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hJ.star
  have hBJ : B * Jᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv J hJ, Matrix.transpose_one]
  have hcancel (X : Matrix (Fin n) (Fin n) ℂ) : B * (Jᵀ * X) = X := by
    rw [← Matrix.mul_assoc, hBJ, Matrix.one_mul]
  have hlast : (Jᴴ)ᵀ * Bᴴ = 1 := by
    have he := congrArg Matrix.conjTranspose hBJ
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose] using he
  change ((Jᴴ * U * B)ᴴ * (Jᴴ * G * J)⁻¹ * (Jᴴ * V * B) * (Jᴴ * G * J)ᵀ).trace = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ,
    Matrix.nonsing_inv_mul_cancel_left _ _ hJH, hcancel]
  calc
    _ = (Bᴴ * (Uᴴ * G⁻¹ * V * Gᵀ) * (Jᴴ)ᵀ).trace := by simp only [Matrix.mul_assoc]
    _ = ((Jᴴ)ᵀ * Bᴴ * (Uᴴ * G⁻¹ * V * Gᵀ)).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [hlast, Matrix.one_mul]; simp only [Matrix.mul_assoc]

theorem positiveTrace_sum_smul {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (c d : Fin r → ℂ)
    (U V : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    ((∑ γ, c γ • U γ)ᴴ * G⁻¹ * (∑ δ, d δ • V δ) * Gᵀ).trace =
      ∑ γ, ∑ δ, (star (c γ) * d δ) * ((U γ)ᴴ * G⁻¹ * V δ * Gᵀ).trace := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_smul, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro δ _
  ring

def positiveTensorContraction {n r : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (D : Fin r → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace

private theorem positive_four_sum_permute {r : ℕ} (f : Fin r → Fin r → Fin r → Fin r → ℂ) :
    (∑ α, ∑ β, ∑ γ, ∑ δ, f α β γ δ) = ∑ γ, ∑ δ, ∑ β, ∑ α, f α β γ δ := by
  let e : (Fin r × Fin r × Fin r × Fin r) ≃ (Fin r × Fin r × Fin r × Fin r) :=
    { toFun := fun ⟨α,β,γ,δ⟩ => (γ,δ,β,α)
      invFun := fun ⟨γ,δ,β,α⟩ => (α,β,γ,δ)
      left_inv := by rintro ⟨α,β,γ,δ⟩; rfl
      right_inv := by rintro ⟨γ,δ,β,α⟩; rfl }
  simpa only [Fintype.sum_prod_type] using Fintype.sum_equiv e
    (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p => f p.2.2.2 p.2.2.1 p.1 p.2.1)
    (by rintro ⟨α,β,γ,δ⟩; rfl)

theorem positiveTensorContraction_fiber {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H C : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    positiveTensorContraction G H (fun α => ∑ γ, C α γ • D γ) =
      positiveTensorContraction G (Cᴴ * H * C) D := by
  unfold positiveTensorContraction
  simp_rw [positiveTrace_sum_smul, Finset.mul_sum]
  rw [positive_four_sum_permute]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro α _
  ring

theorem positiveTensorContraction_coordinates {n r : ℕ}
    (G J : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) (hJ : IsUnit J.det) :
    positiveTensorContraction (Jᴴ * G * J) H (fun α => Jᴴ * D α * (J⁻¹)ᵀ) =
      positiveTensorContraction G H D := by
  unfold positiveTensorContraction
  simp_rw [positiveTrace_coordinate_change G J _ _ hJ]

theorem positiveTensorContraction_smul {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    positiveTensorContraction G H (fun α => c • D α) =
      (Complex.normSq c : ℂ) * positiveTensorContraction G H D := by
  unfold positiveTensorContraction
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_smul, smul_eq_mul, Finset.mul_sum,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem positiveTensorContraction_pullback {n r : ℕ}
    (G J : Matrix (Fin n) (Fin n) ℂ) (H A C : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) (hJ : IsUnit J.det) (hAC : A * C = 1) :
    positiveTensorContraction (Jᴴ * G * J) (Aᴴ * H * A)
      (fun α => J.det • ∑ γ, C α γ • (Jᴴ * D γ * (J⁻¹)ᵀ)) =
      (Complex.normSq J.det : ℂ) * positiveTensorContraction G H D := by
  have hmetric : Cᴴ * (Aᴴ * H * A) * C = H := by
    calc
      _ = (A * C)ᴴ * H * (A * C) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAC]; simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  rw [positiveTensorContraction_smul, positiveTensorContraction_fiber, hmetric,
    positiveTensorContraction_coordinates G J H D hJ]

theorem positiveEnergy_pullback_algebra {n r : ℕ}
    (G J : Matrix (Fin n) (Fin n) ℂ) (H A C : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) (hJ : IsUnit J.det) (hAC : A * C = 1) :
    ((Jᴴ * G * J).det.re)⁻¹ *
      (positiveTensorContraction (Jᴴ * G * J) (Aᴴ * H * A)
        (fun α => J.det • ∑ γ, C α γ • (Jᴴ * D γ * (J⁻¹)ᵀ))).re =
      (G.det.re)⁻¹ * (positiveTensorContraction G H D).re := by
  rw [positiveTensorContraction_pullback G J H A C D hJ hAC, matrix_det_congruence_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hδ : Complex.normSq J.det ≠ 0 := by
    intro hzero
    exact hJ.ne_zero (Complex.normSq_eq_zero.mp hzero)
  rw [mul_inv_rev]
  calc
    _ = (G.det.re)⁻¹ * ((Complex.normSq J.det)⁻¹ * Complex.normSq J.det) *
        (positiveTensorContraction G H D).re := by ring
    _ = _ := by rw [inv_mul_cancel₀ hδ, mul_one]

end Yau.LeafProofs.L14Aux
