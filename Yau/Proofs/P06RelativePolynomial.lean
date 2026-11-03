import Yau.Proofs.P06SpectralClipUnitary
import Yau.Proofs.P06RelativeMatrixClips

noncomputable section
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
variable {n : ℕ}

theorem similarity_mul (L R A B : Matrix (Fin n) (Fin n) ℂ) (hRL : R * L = 1) :
    (L * A * R) * (L * B * R) = L * (A * B) * R := by
  calc
    _ = L * A * (R * L) * B * R := by simp only [mul_assoc]
    _ = _ := by rw [hRL]; simp only [mul_one, mul_assoc]

theorem similarity_pow (L R S : Matrix (Fin n) (Fin n) ℂ)
    (hRL : R * L = 1) (hLR : L * R = 1) (m : ℕ) :
    (L * S * R) ^ m = L * S ^ m * R := by
  induction m with
  | zero => simpa only [pow_zero, mul_one] using hLR.symm
  | succ m hm => rw [pow_succ, hm, similarity_mul L R _ _ hRL, pow_succ]

theorem powerVariation_similarity (L R S D : Matrix (Fin n) (Fin n) ℂ)
    (hRL : R * L = 1) (hLR : L * R = 1) (m : ℕ) :
    powerVariation (L * S * R) (L * D * R) m = L * powerVariation S D m * R := by
  induction m with
  | zero => simp only [powerVariation, mul_zero, zero_mul]
  | succ m hm =>
      rw [powerVariation, hm, similarity_pow L R S hRL hLR,
        similarity_mul L R _ _ hRL, similarity_mul L R _ _ hRL]
      simp only [powerVariation, mul_add, add_mul, mul_assoc]

theorem polynomialVariation_similarity (L R S D : Matrix (Fin n) (Fin n) ℂ)
    (hRL : R * L = 1) (hLR : L * R = 1) (p : Polynomial ℝ) :
    polynomialVariation p (L * S * R) (L * D * R) = L * polynomialVariation p S D * R := by
  classical
  simp only [polynomialVariation, powerVariation_similarity L R S D hRL hLR,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem metricWhiten_metric_mul (H X : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    metricWhiten H (H * X) = metricRoot H * X * (metricRoot H)⁻¹ := by
  calc
    _ = ((metricRoot H)⁻¹ * (metricRoot H * metricRoot H)) * X * (metricRoot H)⁻¹ := by
      rw [metricRoot_sq H hH]
      simp only [metricWhiten, mul_assoc]
    _ = _ := by rw [← mul_assoc, metricRoot_inv_mul H hH, one_mul]

theorem metricSimilarity_inverse_mul (H X : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    metricRoot H * (H⁻¹ * X) * (metricRoot H)⁻¹ = metricWhiten H X := by
  calc
    _ = metricRoot H * (((metricRoot H)⁻¹ * (metricRoot H)⁻¹) * X) * (metricRoot H)⁻¹ := by
      rw [metricRoot_inv_sq H hH]
    _ = metricWhiten H X := by
      simp only [metricWhiten, ← mul_assoc, metricRoot_mul_inv H hH, one_mul]

/-- The original weighted endomorphism differential becomes the genuine
Hermitian matrix differential under the same metric whitening as the
computed form inner product. -/
theorem metricWhiten_polynomialVariation
    (H A D : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (p : Polynomial ℝ) :
    metricWhiten H (H * polynomialVariation p (H⁻¹ * A) (H⁻¹ * D)) =
      polynomialVariation p (metricWhiten H A) (metricWhiten H D) := by
  rw [metricWhiten_metric_mul H _ hH]
  have he := polynomialVariation_similarity (metricRoot H) (metricRoot H)⁻¹
    (H⁻¹ * A) (H⁻¹ * D) (metricRoot_inv_mul H hH) (metricRoot_mul_inv H hH) p
  rw [metricSimilarity_inverse_mul H A hH, metricSimilarity_inverse_mul H D hH] at he
  exact he.symm

theorem relative_polynomialVariation_energy_le
    (H A D : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hA : A.IsHermitian)
    (p : Polynomial ℝ) {R : ℝ}
    (hlam : ∀ i, (metricWhiten_hermitian H A hA).eigenvalues i ∈ Set.Icc (-R) R)
    (hder : ∀ x ∈ Set.Icc (-R) R, |p.derivative.eval x| ≤ 1) :
    ‖relativeMatrixHS H (H * polynomialVariation p (H⁻¹ * A) (H⁻¹ * D))‖ ^ 2 ≤
      ‖relativeMatrixHS H D‖ ^ 2 := by
  simp only [relativeMatrixHS, metricWhiten_polynomialVariation H A D hH p]
  exact polynomialVariation_hermitian_energy_le p _ _ (metricWhiten_hermitian H A hA) hlam hder

end Yau.NodeProofs.P06Aux.Clip
