import Yau.Proofs.F01DiagonalSquareTrace

/-! The native inverse-transpose cotangent convention gives exactly the
weighted coordinate norm in the actual positive diagonal frame. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem dualNormMat_real_diagonal (values : Fin n → ℝ) (hvalues : ∀ i, values i ≠ 0)
    (ξ : Fin n → ℂ) :
    dualNormMat (Matrix.diagonal (fun i => (values i : ℂ))) (WithLp.toLp 2 ξ) =
      ∑ i, (values i)⁻¹ * Complex.normSq (ξ i) := by
  unfold dualNormMat
  rw [inverse_real_diagonal values hvalues, Matrix.diagonal_transpose]
  simp only [WithLp.ofLp_toLp, Matrix.mulVec_diagonal, dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hz : star (ξ i) * ξ i = (Complex.normSq (ξ i) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
  calc
    (star (ξ i) * ((((values i)⁻¹ : ℝ) : ℂ) * ξ i)).re =
        ((((values i)⁻¹ : ℝ) : ℂ) * (star (ξ i) * ξ i)).re := by congr 1; ring
    _ = _ := by rw [hz]; simp

end Yau.NodeProofs.F01Aux
