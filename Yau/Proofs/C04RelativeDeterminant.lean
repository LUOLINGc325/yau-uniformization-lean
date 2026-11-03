import Yau.Proofs.C04MatrixSpectrum
import Yau.Proofs.C04Scaling

/-! A positive metric bounded by its initial metric is bounded below by their determinant ratio. -/

noncomputable section
open scoped ComplexOrder Matrix MatrixOrder

namespace Yau.Proofs.C04Aux

variable {n : ℕ}

theorem relative_determinant_lower (H G : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hG : G.PosDef) (hHG : (G - H).PosSemidef) :
    (H - ((H.det.re / G.det.re : ℝ) : ℂ) • G).PosSemidef := by
  let S := CFC.sqrt G
  have hSsemi : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSunit : IsUnit S := isUnit_mul_self_iff.mp (hSS.symm ▸ hG.isUnit)
  have hS : S.PosDef := hSsemi.posDef_iff_isUnit.mpr hSunit
  have hSinv : S⁻¹.PosDef := hS.inv
  have hu : IsUnit S.det := hSunit.map Matrix.detMonoidHom
  have hBS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hu
  have hSB : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  have hSGS : S⁻¹ * G * S⁻¹ = 1 := by
    calc
      S⁻¹ * G * S⁻¹ = (S⁻¹ * S) * (S * S⁻¹) := by rw [← hSS]; noncomm_ring
      _ = 1 := by rw [hBS, hSB]; simp
  let N := S⁻¹ * H * S⁻¹
  have hN : N.PosDef := by
    simpa only [hSinv.isHermitian.eq] using hH.conjTranspose_mul_mul_same hSinv.mulVec_injective
  have hNupper : (1 - N).PosSemidef := by
    have hh := hHG.conjTranspose_mul_mul_same S⁻¹
    simp only [hSinv.isHermitian.eq] at hh
    rwa [Matrix.mul_sub, Matrix.sub_mul, hSGS] at hh
  have hNlower := determinant_lower_bound hN hNupper
  have hout := hNlower.conjTranspose_mul_mul_same S
  simp only [hS.isHermitian.eq] at hout
  have hSNS : S * N * S = H := by
    calc
      S * N * S = (S * S⁻¹) * H * (S⁻¹ * S) := by dsimp [N]; noncomm_ring
      _ = H := by rw [hSB, hBS]; simp
  have hdiff : S * (N - (N.det.re : ℂ) • 1) * S = H - (N.det.re : ℂ) • G := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hSNS, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hSS]
  rw [hdiff] at hout
  have hdetcore := congrArg Matrix.det hSGS
  simp only [Matrix.det_mul, Matrix.det_one] at hdetcore
  have hdetrel : N.det * G.det = H.det := by
    calc
      N.det * G.det = H.det * (S⁻¹.det * G.det * S⁻¹.det) := by
        dsimp [N]
        rw [Matrix.det_mul, Matrix.det_mul]
        ring
      _ = H.det := by rw [hdetcore, mul_one]
  have hGreal : G.det.im = 0 := (Complex.pos_iff.mp hG.det_pos).2.symm
  have hdetreal : N.det.re * G.det.re = H.det.re := by
    have hh := congrArg Complex.re hdetrel
    simpa only [Complex.mul_re, hGreal, mul_zero, sub_zero] using hh
  have hquot : N.det.re = H.det.re / G.det.re :=
    (eq_div_iff (Complex.pos_iff.mp hG.det_pos).1.ne').mpr hdetreal
  simpa only [hquot] using hout

end Yau.Proofs.C04Aux
