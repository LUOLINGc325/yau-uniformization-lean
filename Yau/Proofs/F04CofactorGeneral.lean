import Yau.Proofs.F04CofactorMatrix

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Yau.F04Proof

variable {n : ℕ}

theorem determinant_re_congruence (G C : Matrix (Fin n) (Fin n) ℂ) :
    (Cᴴ * G * C).det.re = Complex.normSq C.det * G.det.re := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem determinant_ratio_congruence (H G C : Matrix (Fin n) (Fin n) ℂ)
    (hC : IsUnit C.det) :
    (Cᴴ * H * C).det.re / (Cᴴ * G * C).det.re = H.det.re / G.det.re := by
  rw [determinant_re_congruence, determinant_re_congruence]
  exact mul_div_mul_left _ _ (fun hz => hC.ne_zero (Complex.normSq_eq_zero.mp hz))

theorem cofactor_trace_bound (G H : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (hLE : (G - H).PosSemidef) :
    (H.det.re / G.det.re) * traceWith H G ≤ n := by
  let S := CFC.sqrt G
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSdet : S.det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det hSS
    rw [Matrix.det_mul, hz, zero_mul] at he
    exact (ne_of_gt hG.det_pos) he.symm
  have hSpos : S.PosDef := hS.posDef_iff_det_ne_zero.mpr hSdet
  let C := S⁻¹
  have hCpos : C.PosDef := hSpos.inv
  have hCdet : IsUnit C.det := hCpos.isUnit.map Matrix.detMonoidHom
  have hCGC : Cᴴ * G * C = 1 := by
    rw [hCpos.isHermitian.eq, ← hSS]
    change S⁻¹ * (S * S) * S⁻¹ = 1
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hSdet),
      Matrix.one_mul, Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hSdet)]
  let E := Cᴴ * H * C
  have hE : E.PosDef :=
    hH.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hCpos.isUnit)
  have hEle : (1 - E).PosSemidef := by
    have hp := hLE.conjTranspose_mul_mul_same C
    rw [Matrix.mul_sub, Matrix.sub_mul, hCGC] at hp
    exact hp
  have hratio := determinant_ratio_congruence H G C hCdet
  rw [hCGC, Matrix.det_one, Complex.one_re, div_one] at hratio
  have htrace := congrArg Complex.re (LeafProofs.L14Aux.trace_inv_congruence H G C hCdet)
  rw [hCGC] at htrace
  change traceWith E 1 = traceWith H G at htrace
  rw [← hratio, ← htrace]
  exact cofactor_trace_bound_one E hE hEle

end Yau.F04Proof
