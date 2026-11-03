import Yau.Proofs.G01RmAlgebra

noncomputable section
namespace Yau.NodeProofs.G01Aux
open Yau

/-- The actual Hermitian metric gives the Gaussian plane (u,Ju) its expected Gram determinant. -/
theorem gaussianPlane_gram {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (u : V) :
    (2 * (h.toFun u u).re) * (2 * (h.toFun (Complex.I • u) (Complex.I • u)).re) -
      (2 * (h.toFun u (Complex.I • u)).re) ^ 2 = (2 * hermitianNormSq h u) ^ 2 := by
  have hJ : h.toFun (Complex.I • u) (Complex.I • u) = h.toFun u u := by
    rw [h.map_smul_left, h.map_smul_right]
    simp only [Complex.star_def, Complex.conj_I, neg_mul]
    linear_combination -(h.toFun u u) * Complex.I_sq
  have horth : (h.toFun u (Complex.I • u)).re = 0 := by
    rw [h.map_smul_right]
    simp [Complex.mul_re, h.self_adjoint]
  rw [hJ, horth]
  unfold hermitianNormSq
  ring

theorem gaussianPlane_gram_pos {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (u : V) (hu : u ≠ 0) :
    0 < (2 * (h.toFun u u).re) * (2 * (h.toFun (Complex.I • u) (Complex.I • u)).re) -
      (2 * (h.toFun u (Complex.I • u)).re) ^ 2 := by
  rw [gaussianPlane_gram]
  exact sq_pos_of_pos (mul_pos (by norm_num) (hermitianNormSq_pos h hu))

end Yau.NodeProofs.G01Aux
