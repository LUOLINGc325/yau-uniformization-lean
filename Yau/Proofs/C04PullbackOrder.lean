import Yau.Proofs.C04TangentComparison

/-! Actual pullback Gram matrices preserve the metric inequalities at the same point. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem pullbackMat_isHermitian (k : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    (pullbackMat k Φ z).IsHermitian := by
  ext i j
  exact ((k (Φ z)).conjugate_symmetric _ _).symm

theorem pullbackMat_quadratic (k : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n) (u : Fin n → ℂ) :
    star u ⬝ᵥ ((pullbackMat k Φ z) *ᵥ u) =
      (k (Φ z)).toFun
        (∑ i, u i • mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z (stdVec i))
        (∑ i, u i • mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z (stdVec i)) := by
  rw [LeafProofs.L18Aux.hermitian_sum_left]
  simp only [LeafProofs.L18Aux.hermitian_sum_right,
    HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, pullbackMat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pullbackMat_order_real (k g : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n) (c : ℝ)
    (hkg : HermLE (gMat k (Φ z)) ((c : ℂ) • gMat g (Φ z))) :
    HermLE (pullbackMat k Φ z) ((c : ℂ) • pullbackMat g Φ z) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact ((pullbackMat_isHermitian g Φ z).smul (by simp [IsSelfAdjoint])).sub
      (pullbackMat_isHermitian k Φ z)
  · intro u
    let v := ∑ i, u i • mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z (stdVec i)
    have hnorm := tangent_norm_le_of_HermLE k g (Φ z) c hkg v
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, pullbackMat_quadratic]
    apply Complex.nonneg_iff.mpr
    constructor
    · simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hermitianNormSq, v] using sub_nonneg.mpr hnorm
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, (g (Φ z)).self_adjoint, (k (Φ z)).self_adjoint, mul_zero, sub_self]

theorem pullbackMat_order (k g : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n)
    (hkg : HermLE (gMat k (Φ z)) (gMat g (Φ z))) :
    HermLE (pullbackMat k Φ z) (pullbackMat g Φ z) := by
  simpa only [Complex.ofReal_one, one_smul] using pullbackMat_order_real k g Φ z 1
    (by simpa only [Complex.ofReal_one, one_smul] using hkg)

end Yau.Proofs.C04Aux
