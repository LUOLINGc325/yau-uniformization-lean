import Yau.LeafProofs.L12

/-! The fixed real coordinate vectors form an orthonormal basis of the
complex Euclidean model, including dimension zero. -/

noncomputable section
open scoped Topology InnerProductSpace

namespace Yau.Proofs.C04Aux
open Yau Yau.LeafProofs.L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

def normalEllipticRealBasis (n : ℕ) : OrthonormalBasis (RIdx n) ℝ (ComplexVector n) :=
  (Pi.orthonormalBasis fun _ : Fin n => Complex.orthonormalBasisOneI).reindex
    (Equiv.sigmaEquivProd (Fin n) (Fin 2))

@[simp] theorem normalEllipticRealBasis_apply {n : ℕ} (a : RIdx n) :
    normalEllipticRealBasis n a = realVec a := by
  rcases a with ⟨i, j⟩
  rw [normalEllipticRealBasis, OrthonormalBasis.reindex_apply]
  change Pi.orthonormalBasis (fun _ : Fin n => Complex.orthonormalBasisOneI) ⟨i, j⟩ = _
  rw [Pi.orthonormalBasis_apply]
  fin_cases j <;> ext k <;>
    simp [realVec, Complex.coe_orthonormalBasisOneI, EuclideanSpace.single, Pi.single_apply]

@[simp] theorem normalEllipticRealBasis_repr {n : ℕ} (v : ComplexVector n) (a : RIdx n) :
    (normalEllipticRealBasis n).repr v a = realCoord v a := by
  have hb : (normalEllipticRealBasis n).toBasis = realVec_basis n := by
    ext i
    simp only [OrthonormalBasis.coe_toBasis, normalEllipticRealBasis_apply, realVec_basis_apply]
  rw [← OrthonormalBasis.coe_toBasis_repr_apply, hb, realVec_basis_repr]

theorem normal_elliptic_realCoord_inner {n : ℕ} (v : ComplexVector n) (a : RIdx n) :
    realCoord v a = ⟪realVec a, v⟫_ℝ := by
  rw [← normalEllipticRealBasis_repr, OrthonormalBasis.repr_apply_apply,
    normalEllipticRealBasis_apply]

theorem normal_elliptic_norm_sq {n : ℕ} (v : ComplexVector n) :
    ‖v‖ ^ 2 = ∑ a : RIdx n, (realCoord v a) ^ 2 := by
  have hh := ((normalEllipticRealBasis n).sum_sq_norm_inner_right v).symm
  simpa only [← OrthonormalBasis.repr_apply_apply, normalEllipticRealBasis_repr,
    Real.norm_eq_abs, sq_abs] using hh

end Yau.Proofs.C04Aux
