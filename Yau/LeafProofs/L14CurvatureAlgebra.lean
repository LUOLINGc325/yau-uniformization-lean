import Yau.LeafProofs.L14

/-! Algebraic change-of-chart identities for the L14 curvature factor. -/

noncomputable section

open scoped Matrix

namespace Yau.LeafProofs

theorem raised_coefficients_change {n r : ℕ}
    (G J : Matrix (Fin n) (Fin n) ℂ)
    (A C : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin n) (Fin r) ℂ)
    (hJ : IsUnit J.det) (hAC : A * C = 1) :
    J * ((Jᴴ * G * J)⁻¹ * (J.det • (Jᴴ * F * Cᵀ))) * Aᵀ =
      J.det • (G⁻¹ * F) := by
  have hstar : IsUnit (Jᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hJ.star
  have hCA : Cᵀ * Aᵀ = 1 := by
    rw [← Matrix.transpose_mul, hAC, Matrix.transpose_one]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ hstar,
    Matrix.mul_nonsing_inv_cancel_left _ _ hJ, hCA, Matrix.mul_one]

private theorem sum_four_swap {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (f : ι → κ → α → β → ℂ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) =
      ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  classical
  calc
    _ = ∑ i, ∑ a, ∑ j, ∑ b, f i j a b := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j, ∑ b, f i j a b := by rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ b, ∑ j, f i j a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

private theorem curvature_sesquilinear_sum {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) :
    (∑ α, ∑ β, B α β * star (v α) * u β) =
      star v ⬝ᵥ (B *ᵥ u) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  ring

private theorem curvature_sesquilinear_conjugate {r : ℕ}
    (B A : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) :
    (∑ α, ∑ β, (Aᴴ * B * A) α β * star (v α) * u β) =
      ∑ α, ∑ β, B α β * star ((A *ᵥ v) α) * (A *ᵥ u) β := by
  rw [curvature_sesquilinear_sum, curvature_sesquilinear_sum]
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_assoc]

theorem nakanoComplexSum_gauge {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (W : Matrix (Fin n) (Fin r) ℂ) :
    (∑ i, ∑ j, ∑ α, ∑ β,
      (Aᴴ * R i j * A) α β * star (W j α) * W i β) =
      ∑ i, ∑ j, ∑ α, ∑ β,
        R i j α β * star ((W * Aᵀ) j α) * (W * Aᵀ) i β := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h (k : Fin n) (α : Fin r) : (A *ᵥ W k) α = (W * Aᵀ) k α := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro β _
    ring
  simpa only [h] using curvature_sesquilinear_conjugate (R i j) A (W i) (W j)

private theorem curvature_coordinate_contraction {n : ℕ}
    (R J : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    (∑ i, ∑ j, (∑ p, ∑ q, (J p i * star (J q j)) * R p q) * star (v j) * u i) =
      ∑ p, ∑ q, R p q * star ((J *ᵥ v) q) * (J *ᵥ u) p := by
  simp only [Finset.sum_mul]
  rw [sum_four_swap]
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem nakanoComplexSum_coordinates {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (J : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin r) ℂ) :
    (∑ i, ∑ j, ∑ α, ∑ β,
      (∑ p, ∑ q, (J p i * star (J q j)) • R p q) α β * star (W j α) * W i β) =
      ∑ p, ∑ q, ∑ α, ∑ β,
        R p q α β * star ((J * W) q α) * (J * W) p β := by
  rw [sum_four_swap, sum_four_swap (fun p q α β =>
    R p q α β * star ((J * W) q α) * (J * W) p β)]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Matrix.mul_apply] using
    curvature_coordinate_contraction (fun p q => R p q α β) J
      (fun i => W i β) (fun j => W j α)

theorem nakanoComplexSum_pullback {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (J : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin r) (Fin r) ℂ)
    (W : Matrix (Fin n) (Fin r) ℂ) :
    (∑ i, ∑ j, ∑ α, ∑ β,
      (Aᴴ * (∑ p, ∑ q, (J p i * star (J q j)) • R p q) * A) α β *
        star (W j α) * W i β) =
      ∑ i, ∑ j, ∑ α, ∑ β,
        R i j α β * star ((J * W * Aᵀ) j α) * (J * W * Aᵀ) i β := by
  rw [nakanoComplexSum_gauge, nakanoComplexSum_coordinates, Matrix.mul_assoc]

theorem nakanoQuadratic_pullback {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (J : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin r) (Fin r) ℂ)
    (W : Matrix (Fin n) (Fin r) ℂ) :
    BundleDbar.nakanoQuadratic
      (fun i j => Aᴴ * (∑ p, ∑ q, (J p i * star (J q j)) • R p q) * A) W =
      BundleDbar.nakanoQuadratic R (J * W * Aᵀ) := by
  exact congrArg Complex.re (nakanoComplexSum_pullback R J A W)

theorem matrix_det_congruence_re {n : ℕ} (G J : Matrix (Fin n) (Fin n) ℂ) :
    (Jᴴ * G * J).det.re = Complex.normSq J.det * G.det.re := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

end Yau.LeafProofs
