import Yau.Proofs.F01LargestRayleigh
import Yau.Proofs.F01LeviOrder

/-! The actual supremum of Rayleigh quotients gives the exact Hermitian
upper order. A strictly larger scalar gives genuine positive definiteness. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ}

theorem order_of_largestMatrixRayleigh_le {G H : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) (hH : H.PosDef) {c : ℝ}
    (hc : largestMatrixRayleigh G H ≤ c) :
    ((c : ℂ) • G - H).PosSemidef := by
  apply (matrix_posSemidef_sub_iff_quadratic hH.isHermitian
    (hG.isHermitian.smul (show IsSelfAdjoint (c : ℂ) from Complex.conj_ofReal c))).mpr
  intro v
  by_cases hv : v = 0
  · subst v
    simp
  · have hd := matrixQuadraticValue_pos hG hv
    have hr := (matrixRayleigh_le_largest hG hH v).trans hc
    have hq : matrixQuadraticValue H v ≤ c * matrixQuadraticValue G v :=
      (div_le_iff₀ hd).mp hr
    simpa only [matrixQuadraticValue, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hq

theorem posDef_of_largestMatrixRayleigh_lt {G H : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) (hH : H.PosDef) {c : ℝ}
    (hc : largestMatrixRayleigh G H < c) :
    ((c : ℂ) • G - H).PosDef := by
  have hpos : (((c - largestMatrixRayleigh G H : ℝ) : ℂ) • G).PosDef :=
    hG.smul (Complex.zero_lt_real.mpr (sub_pos.mpr hc))
  have hsem := order_of_largestMatrixRayleigh_le hG hH (le_refl (largestMatrixRayleigh G H))
  convert! hpos.add_posSemidef hsem using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_sub]
  ring

end Yau.NodeProofs.F01Aux
