import Yau.Blueprint.Nodes
import Mathlib.Analysis.Matrix.Order

open Matrix
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {ι : Type*} [Fintype ι]

theorem hermitian_posSemidef_iff_re_quadratic_nonneg (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    H.PosSemidef ↔ ∀ v : ι → ℂ, 0 ≤ (star v ⬝ᵥ (H*ᵥv)).re := by
  constructor
  · intro h v
    exact (RCLike.nonneg_iff.mp (h.dotProduct_mulVec_nonneg v)).1
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
    intro v
    have hi := congrArg Complex.im (hH.star_dotProduct_mulVec_comm v v)
    simp only [Complex.star_def,Complex.conj_im] at hi
    exact Complex.nonneg_iff.mpr ⟨h v,by linarith⟩

theorem hermitian_eq_of_re_quadratic_eq (H K : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hEq : ∀ v : ι → ℂ, (star v ⬝ᵥ (H*ᵥv)).re = (star v ⬝ᵥ (K*ᵥv)).re) : H = K := by
  apply le_antisymm
  · apply Matrix.le_iff.mpr
    apply (hermitian_posSemidef_iff_re_quadratic_nonneg (K-H) (hK.sub hH)).mpr
    intro v
    rw [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re,←hEq v,sub_self]
  · apply Matrix.le_iff.mpr
    apply (hermitian_posSemidef_iff_re_quadratic_nonneg (H-K) (hH.sub hK)).mpr
    intro v
    rw [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re,hEq v,sub_self]

end Yau.NodeProofs.E02Aux
