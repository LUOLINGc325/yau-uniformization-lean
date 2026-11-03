import Yau.Proofs.C04ChartDistortion

/-! The determinant ratio in an actual h-unitary coordinate frame. -/

noncomputable section
open scoped ComplexOrder Matrix

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem unitary_gram_determinant (H G P : Herm n) (hgram : P.conjTranspose * H * P = 1) :
    (P.conjTranspose * G * P).det * H.det = G.det := by
  have hh := congrArg Matrix.det hgram
  simp only [Matrix.det_mul, Matrix.det_one] at hh
  calc
    (P.conjTranspose * G * P).det * H.det =
        G.det * (P.conjTranspose.det * H.det * P.det) := by
      rw [Matrix.det_mul, Matrix.det_mul]
      ring
    _ = G.det := by rw [hh, mul_one]

theorem unitary_gram_determinant_re (H G P : Herm n) (hH : H.PosDef)
    (hgram : P.conjTranspose * H * P = 1) :
    (P.conjTranspose * G * P).det.re = G.det.re / H.det.re := by
  have hi : H.det.im = 0 := (Complex.pos_iff.mp hH.det_pos).2.symm
  have hh := congrArg Complex.re (unitary_gram_determinant H G P hgram)
  simp only [Complex.mul_re, hi, mul_zero, sub_zero] at hh
  exact (eq_div_iff (Complex.pos_iff.mp hH.det_pos).1.ne').mpr hh

end Yau.Proofs.C04Aux
