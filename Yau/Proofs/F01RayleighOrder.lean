import Yau.Proofs.F01RayleighBasis
import Yau.Proofs.F01MatrixComparison

/-! Genuine Hermitian order bounds the actual Rayleigh quotients, including
the zero vector used in the range definition. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixQuadraticValue_pos {H : Matrix ι ι ℂ} (hH : H.PosDef)
    {v : ι → ℂ} (hv : v ≠ 0) : 0 < matrixQuadraticValue H v :=
  (Complex.pos_iff.mp (hH.dotProduct_mulVec_pos hv)).1

theorem matrixQuadraticValue_nonneg {H : Matrix ι ι ℂ} (hH : H.PosSemidef)
    (v : ι → ℂ) : 0 ≤ matrixQuadraticValue H v :=
  (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg v)).1

theorem matrixRayleigh_le_of_posSemidef {H K : Matrix ι ι ℂ}
    (hH : H.PosDef) {C : ℝ} (hC : 0 ≤ C)
    (horder : ((C : ℂ) • H - K).PosSemidef) (v : ι → ℂ) :
    matrixRayleigh H K v ≤ C := by
  by_cases hv : v = 0
  · subst v
    simpa [matrixRayleigh, matrixQuadraticValue] using hC
  · have hden := matrixQuadraticValue_pos hH hv
    have ho := matrixQuadraticValue_nonneg horder v
    have hh : 0 ≤ C * matrixQuadraticValue H v - matrixQuadraticValue K v := by
      simpa only [matrixQuadraticValue, Matrix.sub_mulVec, Matrix.smul_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using ho
    exact (div_le_iff₀ hden).mpr (by linarith)

theorem matrixRayleigh_nonneg {H K : Matrix ι ι ℂ}
    (hH : H.PosSemidef) (hK : K.PosSemidef) (v : ι → ℂ) :
    0 ≤ matrixRayleigh H K v :=
  div_nonneg (matrixQuadraticValue_nonneg hK v) (matrixQuadraticValue_nonneg hH v)

end Yau.NodeProofs.F01Aux
