import Yau.Proofs.Y03Frames

/-! The exact inverse bound for a nonsingular contraction, including dimension zero. -/

noncomputable section

namespace Yau.Proofs.C07Aux

set_option maxHeartbeats 800000

open Yau Yau.Blueprint Yau.Blueprint.Alignment
open Yau.Blueprint.Alignment.Y03Proof
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

theorem contraction_inverse_norm (A : Herm n) (hdet : A.det ≠ 0)
    (hA : matOpNorm A ≤ 1) :
    matOpNorm A⁻¹ ≤ ‖A.det‖⁻¹ := by
  classical
  obtain ⟨U, V, σ, hU, hV, hσ, _, hdiag⟩ :=
    positive_sorted_contraction_svd A hdet hA
  have hnormσ : ∀ i, ‖(σ i : ℂ)‖ = σ i :=
    fun i => Complex.norm_of_nonneg (hσ i).1.le
  have hprod : ‖A.det‖ = ∏ i, σ i := by
    have hd := congrArg (fun B : Herm n => ‖B.det‖) hdiag
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal,
      norm_mul, norm_star, norm_prod, hnormσ, norm_det_unitary hU,
      norm_det_unitary hV, one_mul, mul_one] using hd
  have hdetpos : 0 < ‖A.det‖ := norm_pos_iff.mpr hdet
  have hprodle : ∀ i, ‖A.det‖ ≤ σ i := by
    intro i
    rw [hprod, ← Finset.mul_prod_erase Finset.univ σ (Finset.mem_univ i)]
    exact mul_le_of_le_one_right (hσ i).1.le
      (Finset.prod_le_one₀ (fun j _ => (hσ j).1.le) (fun j _ => (hσ j).2))
  have hdiaginv : ((Matrix.diagonal (fun i => (σ i : ℂ)) : Herm n)⁻¹) =
      Matrix.diagonal (fun i => (σ i : ℂ)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hσ i).1.ne')
  have hdiagbound : matOpNorm ((Matrix.diagonal (fun i => (σ i : ℂ)) : Herm n)⁻¹) ≤
      ‖A.det‖⁻¹ := by
    rw [hdiaginv]
    change ‖Matrix.diagonal (fun i => (σ i : ℂ)⁻¹)‖ ≤ _
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hdetpos.le)).mpr
    intro i
    rw [norm_inv, hnormσ]
    exact (inv_le_inv₀ (hσ i).1 hdetpos).mpr (hprodle i)
  have hVinv : V⁻¹ = V.conjTranspose := Matrix.inv_eq_left_inv hV.1
  have hUinv : U.conjTranspose⁻¹ = U := Matrix.inv_eq_left_inv hU.2
  have hinv := congrArg (fun B : Herm n => matOpNorm B⁻¹) hdiag
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hVinv, hUinv,
    matOpNorm_unitary_mul (unitary_conjTranspose hV), matOpNorm_mul_unitary hU] at hinv
  exact hinv ▸ hdiagbound

theorem centerDeriv_inverse_norm (F : ComplexVector n → ComplexVector n)
    (hdet : LinearMap.det (centerDeriv F).toLinearMap ≠ 0)
    (hF : ‖centerDeriv F‖ ≤ 1) :
    ‖(centerDeriv F).inverse‖ ≤
      ‖LinearMap.det (centerDeriv F).toLinearMap‖⁻¹ := by
  let A := derivativeMatrix F
  have hA : A.det ≠ 0 := by simpa only [A, derivativeMatrix_det] using hdet
  let L := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hinverse : (centerDeriv F).inverse = L (A⁻¹) := by
    apply ContinuousLinearMap.inverse_eq
    · rw [← derivativeMatrix_toEuclideanCLM]
      change L A * L (A⁻¹) = 1
      rw [← map_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), map_one]
    · rw [← derivativeMatrix_toEuclideanCLM]
      change L (A⁻¹) * L A = 1
      rw [← map_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), map_one]
  rw [hinverse]
  change matOpNorm A⁻¹ ≤ _
  simpa only [A, derivativeMatrix_det] using
    contraction_inverse_norm A hA (by simpa only [A, matOpNorm_derivativeMatrix] using hF)

theorem centerDeriv_inverse_norm_of_det_exp
    (F : ComplexVector n → ComplexVector n) (δ : ℝ)
    (hdet : ‖LinearMap.det (centerDeriv F).toLinearMap‖ = Real.exp (-δ))
    (hF : ‖centerDeriv F‖ ≤ 1) :
    ‖(centerDeriv F).inverse‖ ≤ Real.exp δ := by
  have hne : LinearMap.det (centerDeriv F).toLinearMap ≠ 0 := by
    intro hz
    have hpos := Real.exp_pos (-δ)
    rw [hz, norm_zero] at hdet
    linarith
  simpa only [hdet, Real.exp_neg, inv_inv] using centerDeriv_inverse_norm F hne hF

end Yau.Proofs.C07Aux
