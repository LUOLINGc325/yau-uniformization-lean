import Yau.Proofs.E02CotangentTensor
import Yau.Proofs.E02MatrixBasic

open Matrix
open scoped Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

theorem cotangent_vertical_quadratic {n : ℕ}
    (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (V : ComplexVector n) :
    star (cotangentVector 0 V) ⬝ᵥ (W*ᵥcotangentVector 0 V) =
      star (WithLp.ofLp V) ⬝ᵥ (W.toBlocks₂₂*ᵥWithLp.ofLp V) := by
  simp [cotangentVector,dotProduct,Matrix.mulVec,Matrix.toBlocks₂₂]

/-- The positive contact weight is cancelled only under its actual
strict positivity. The conclusion is order of the genuine vertical block. -/
theorem verticalBlock_order_of_weighted_quadratic {n : ℕ}
    (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hW : W.IsHermitian)
    (B : Herm n) (hB : B.IsHermitian) (α c : ℝ) (hα : 0 < α)
    (hLower : ∀ V : ComplexVector n, α*c*qform B V ≤
      α*(star (cotangentVector 0 V) ⬝ᵥ (W*ᵥcotangentVector 0 V)).re) :
    (W.toBlocks₂₂-(c : ℂ) • B).PosSemidef := by
  have hC : W.toBlocks₂₂.IsHermitian := hW.submatrix Sum.inr
  have hc : IsSelfAdjoint (c : ℂ) := by simp [isSelfAdjoint_iff]
  apply (hermitian_posSemidef_iff_re_quadratic_nonneg _ (hC.sub (hB.smul hc))).mpr
  intro v
  let V : ComplexVector n := WithLp.toLp 2 v
  have hV := hLower V
  rw [cotangent_vertical_quadratic] at hV
  have hScalar : c*qform B V ≤ (star v ⬝ᵥ (W.toBlocks₂₂*ᵥv)).re := by
    apply (mul_le_mul_iff_right₀ hα).mp
    simpa only [V,WithLp.ofLp_toLp,mul_assoc,mul_comm α] using hV
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,
    Complex.sub_re]
  simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  exact sub_nonneg.mpr hScalar

end Yau.NodeProofs.E02Aux
