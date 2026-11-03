import Yau.LeafProofs.L05ABPQuadraticPolynomial

noncomputable section

open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem realVec_coordinates_sum {n : ℕ} (v : Space n) :
    ∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) v • Yau.realVec i=v := by
  simpa only [OrthonormalBasis.repr_apply_apply,complexVector_realOrthonormalBasis_apply] using
    (complexVector_realOrthonormalBasis n).sum_repr v

theorem realVec_coordinates_norm_sq {n : ℕ} (v : Space n) :
    ∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) v*inner ℝ (Yau.realVec i) v=‖v‖^2 := by
  have he := (complexVector_realOrthonormalBasis n).sum_inner_mul_inner v v
  simp only [complexVector_realOrthonormalBasis_apply,real_inner_self_eq_norm_sq] at he
  simpa only [real_inner_comm v] using he

theorem jointHessian_quadratic_form {n : ℕ}
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v) (v : Space n) :
    (fun i => inner ℝ (Yau.realVec i) v) ⬝ᵥ
      ((jointHessian B : Mat n)*ᵥ(fun i => inner ℝ (Yau.realVec i) v))=
        B (v,0) (v,0) := by
  have hp : (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) v • ((Yau.realVec i,0) : Point n))=(v,0) := by
    have he := congrArg (ContinuousLinearMap.inl ℝ (Space n) ℝ) (realVec_coordinates_sum v)
    simpa only [map_sum,map_smul,ContinuousLinearMap.inl_apply] using he
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,jointHessian_coe_apply B hB]
  rw [←hp]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB (Yau.realVec j,0) (Yau.realVec i,0)]
  ring

theorem jointHessian_spatial_form_bounds {n : ℕ} {delta : ℝ} (hdelta : 0<delta)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v)
    (hneg : (-(jointHessian B : Mat n)).PosSemidef)
    (hlow : ((jointHessian B : Mat n)+delta⁻¹ • (1 : Mat n)).PosSemidef) :
    (∀ v : Space n, 0≤-B (v,0) (v,0)) ∧
      (∀ v : Space n, delta*(-B (v,0) (v,0))≤‖v‖^2) := by
  constructor
  · intro v
    have hh := hneg.dotProduct_mulVec_nonneg (fun i => inner ℝ (Yau.realVec i) v)
    simp only [Pi.star_apply,star_trivial,Matrix.neg_mulVec,dotProduct_neg] at hh
    rwa [jointHessian_quadratic_form B hB v] at hh
  · intro v
    have hh := hlow.dotProduct_mulVec_nonneg (fun i => inner ℝ (Yau.realVec i) v)
    simp only [Pi.star_apply,star_trivial,Matrix.add_mulVec,Matrix.smul_mulVec,
      Matrix.one_mulVec,dotProduct_add,dotProduct_smul,jointHessian_quadratic_form B hB v] at hh
    change 0≤B (v,0) (v,0)+delta⁻¹*
      (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) v*inner ℝ (Yau.realVec i) v) at hh
    rw [realVec_coordinates_norm_sq] at hh
    have hm := mul_nonneg hdelta.le hh
    rw [mul_add,←mul_assoc,mul_inv_cancel₀ hdelta.ne',one_mul] at hm
    linarith

end Yau.LeafProofs.L05Aux
