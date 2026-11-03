import Yau.Proofs.P06WeitzenbockSpectralCurvature

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.P06Weitzenbock
variable {n : ℕ}

theorem inverseMetric_eq_unitary_frame (H E : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hE : Eᴴ * H * E = 1) : H⁻¹ = E * Eᴴ := by
  have he : E * (Eᴴ * H) = 1 := (mul_eq_one_comm).mp hE
  have hInv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (hH.isUnit.map Matrix.detMonoidHom)
  calc
    H⁻¹ = 1 * H⁻¹ := by rw [Matrix.one_mul]
    _ = (E * (Eᴴ * H)) * H⁻¹ := by rw [he]
    _ = (E * Eᴴ) * (H * H⁻¹) := by noncomm_ring
    _ = _ := by rw [hInv, Matrix.mul_one]

theorem raised_spectral_form (H E : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (D : Matrix (Fin n) (Fin n) ℂ) :
    H⁻¹ * (H * E * D * Eᴴ * H) * H⁻¹ = E * D * Eᴴ := by
  have hInv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (hH.isUnit.map Matrix.detMonoidHom)
  have hInv' : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (hH.isUnit.map Matrix.detMonoidHom)
  calc
    _ = (H⁻¹ * H) * (E * D * Eᴴ) * (H * H⁻¹) := by noncomm_ring
    _ = _ := by rw [hInv, hInv']; simp only [Matrix.one_mul, Matrix.mul_one]

theorem raised_spectral_square (H E : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (hE : Eᴴ * H * E = 1) (D : Matrix (Fin n) (Fin n) ℂ) :
    H⁻¹ * (H * E * D * Eᴴ * H) * H⁻¹ * (H * E * D * Eᴴ * H) * H⁻¹ =
      E * (D * D) * Eᴴ := by
  have hInv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (hH.isUnit.map Matrix.detMonoidHom)
  have hInv' : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (hH.isUnit.map Matrix.detMonoidHom)
  calc
    _ = (H⁻¹ * H) * E * D * Eᴴ * (H * H⁻¹) * H * E * D * Eᴴ * (H * H⁻¹) := by noncomm_ring
    _ = E * D * (Eᴴ * H * E) * D * Eᴴ := by rw [hInv, hInv']; noncomm_ring
    _ = _ := by rw [hE]; noncomm_ring

theorem spectral_square_sum_swap (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, r i j = r j i) (eig : Fin n → ℝ) :
    (∑ i, ∑ j, r i j * (eig j) ^ 2) = ∑ i, ∑ j, r i j * (eig i) ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hr j i]

theorem spectral_curvature_energy_real (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, r i j = r j i) (eig : Fin n → ℝ) :
    2 * (∑ i, ∑ j, r i j * (eig j) ^ 2) -
      2 * (∑ i, ∑ j, r i j * eig i * eig j) = diagonalCurvatureEnergy r eig := by
  rw [spectral_square_sum_swap r hr eig, ← diagonalReaction_pairing r hr eig]
  simp only [diagonalReaction, Finset.sum_mul, Finset.mul_sum]
  have hterm (i j : Fin n) : 2 * (r i j * (eig i - eig j)) * eig i =
      2 * (r i j * eig i ^ 2) - 2 * (r i j * eig i * eig j) := by ring
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem curvatureContraction_spectral_energy
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j k l, R i j k l = R k l i j)
    (E : Matrix (Fin n) (Fin n) ℂ) (eig : Fin n → ℝ) :
    (2 * curvatureContraction R (E * Eᴴ)
        (E * Matrix.diagonal (fun i => (((eig i) ^ 2 : ℝ) : ℂ)) * Eᴴ) -
      2 * curvatureContraction R (E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ)
        (E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ)).re =
      diagonalCurvatureEnergy (fun i j => (frameCurvatureCoefficient R E i j).re) eig := by
  have hOne : E * Eᴴ = E * Matrix.diagonal (fun _ : Fin n => (1 : ℂ)) * Eᴴ := by
    simp only [Matrix.diagonal_one, Matrix.mul_one]
  rw [hOne]
  have hp := curvatureContraction_spectral_re R E (fun _ => 1) (fun i => (eig i) ^ 2)
  have hq := curvatureContraction_spectral_re R E eig eig
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [Complex.sub_re, Complex.mul_re, h2re, h2im, zero_mul, sub_zero]
  have hc : (fun _ : Fin n => ((1 : ℝ) : ℂ)) = (fun _ => (1 : ℂ)) := by
    funext i
    rfl
  rw [hc] at hp
  rw [hp, hq]
  simp only [one_mul]
  have hs (i j : Fin n) : (frameCurvatureCoefficient R E i j).re =
      (frameCurvatureCoefficient R E j i).re :=
    congrArg Complex.re (frameCurvatureCoefficient_comm R hR E i j)
  convert spectral_curvature_energy_real _ hs eig using 1 <;>
    congr 2 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> ring

end Yau.NodeProofs.P06Weitzenbock
