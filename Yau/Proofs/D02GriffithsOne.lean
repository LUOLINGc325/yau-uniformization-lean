import Yau.Proofs.D02PullbackCurvatureCenter

/-! Algebra for the actual one-dimensional base curvature transition. -/

noncomputable section
open scoped Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint.V03Proof

theorem griffithsQuadratic_one {r : ℕ}
    (R : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℂ)
    (ξ : ComplexVector 1) (v : ComplexVector r) :
    BundleDbar.griffithsQuadratic R ξ v = ‖ξ 0‖ ^ 2 *
      (star (WithLp.ofLp v) ⬝ᵥ R 0 0 *ᵥ WithLp.ofLp v).re := by
  have he : (∑ α, ∑ β, R 0 0 α β * ξ 0 * star (ξ 0) * star (v α) * v β) =
      (star (ξ 0) * ξ 0) * (star (WithLp.ofLp v) ⬝ᵥ R 0 0 *ᵥ WithLp.ofLp v) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  unfold BundleDbar.griffithsQuadratic
  simp only [Fin.sum_univ_one]
  rw [he, star_mul_self_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem real_quadratic_congruence {r s : ℕ} (R : Matrix (Fin r) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin s) ℂ) (v : Fin s → ℂ) :
    star v ⬝ᵥ (Aᴴ * R * A) *ᵥ v = star (A *ᵥ v) ⬝ᵥ R *ᵥ (A *ᵥ v) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem griffiths_one_congruence_nonneg {r : ℕ}
    (R : Matrix (Fin r) (Fin r) ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (d : ℂ)
    (hR : ∀ v : Fin r → ℂ, 0 ≤ (star v ⬝ᵥ R *ᵥ v).re)
    (ξ : ComplexVector 1) (v : ComplexVector r) :
    0 ≤ BundleDbar.griffithsQuadratic
      (fun _ _ : Fin 1 => Aᴴ * ((d * star d) • R) * A) ξ v := by
  rw [griffithsQuadratic_one]
  have hd : d * star d = (‖d‖ ^ 2 : ℝ) := by rw [mul_comm, star_mul_self_eq_norm_sq]
  rw [hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, dotProduct_smul,
    real_quadratic_congruence]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hR _))

end Yau.NodeProofs.D02Aux
