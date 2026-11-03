import Yau.Geometry.Basic

/-! Actual Hermitian products used in the pullback-field extension. -/

namespace Yau.Proofs.C03Aux
open Yau

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def pullbackHermitian (h : HermitianInnerProduct W) (L : V →ₗ[ℂ] W)
    (hL : Function.Injective L) : HermitianInnerProduct V where
  toFun u v := h.toFun (L u) (L v)
  map_add_left := by intros; simp only [map_add, h.map_add_left]
  map_smul_left := by intros; simp only [map_smul, h.map_smul_left]
  map_add_right := by intros; simp only [map_add, h.map_add_right]
  map_smul_right := by intros; simp only [map_smul, h.map_smul_right]
  conjugate_symmetric := fun u v => h.conjugate_symmetric (L u) (L v)
  self_adjoint := fun u => h.self_adjoint (L u)
  positive_definite := by
    intro u
    refine ⟨(h.positive_definite (L u)).1, ?_⟩
    rw [(h.positive_definite (L u)).2]
    exact ⟨fun hu => hL (by simpa only [map_zero] using hu), fun hu => by simp [hu]⟩

def blendHermitian (h k : HermitianInnerProduct V) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : HermitianInnerProduct V where
  toFun u v := (t : ℂ) * h.toFun u v + ((1 - t : ℝ) : ℂ) * k.toFun u v
  map_add_left := by intros; simp only [h.map_add_left, k.map_add_left]; ring
  map_smul_left := by intros; simp only [h.map_smul_left, k.map_smul_left]; ring
  map_add_right := by intros; simp only [h.map_add_right, k.map_add_right]; ring
  map_smul_right := by intros; simp only [h.map_smul_right, k.map_smul_right]; ring
  conjugate_symmetric := by
    intro u v
    rw [h.conjugate_symmetric u v, k.conjugate_symmetric u v]
    simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  self_adjoint := by
    intro u
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, zero_mul,
      h.self_adjoint, k.self_adjoint, mul_zero, add_zero]
  positive_definite := by
    intro u
    have he : ((t : ℂ) * h.toFun u u + ((1 - t : ℝ) : ℂ) * k.toFun u u).re =
        t * hermitianNormSq h u + (1 - t) * hermitianNormSq k u := by
      simp [hermitianNormSq, Complex.mul_re]
    rw [he]
    have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    refine ⟨add_nonneg (mul_nonneg ht (hermitianNormSq_nonneg h u))
      (mul_nonneg ht' (hermitianNormSq_nonneg k u)), ?_⟩
    constructor
    · intro hz
      by_contra hu
      have hh := hermitianNormSq_pos h hu
      have hk := hermitianNormSq_pos k hu
      have hp : 0 < t * hermitianNormSq h u + (1 - t) * hermitianNormSq k u := by
        by_cases ht0 : t = 0
        · simpa [ht0] using hk
        · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) hh)
            (mul_nonneg ht' hk.le)
      exact hp.ne' hz
    · rintro rfl
      have hh := (h.positive_definite 0).2.mpr rfl
      have hk := (k.positive_definite 0).2.mpr rfl
      simp only [hermitianNormSq, hh, hk, mul_zero, add_zero]

theorem blendHermitian_at_one (h k : HermitianInnerProduct V) (u v : V) :
    (blendHermitian h k 1 (by norm_num) le_rfl).toFun u v = h.toFun u v := by
  simp [blendHermitian]

theorem blendHermitian_at_zero (h k : HermitianInnerProduct V) (u v : V) :
    (blendHermitian h k 0 le_rfl (by norm_num)).toFun u v = k.toFun u v := by
  simp [blendHermitian]

end Yau.Proofs.C03Aux
