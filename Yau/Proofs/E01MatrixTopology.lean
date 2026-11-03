import Yau.Proofs.E01Matrix

/-! Closed quadratic constraints in the actual finite-dimensional matrix space. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem continuous_ellipsoidQuadratic (η : ComplexVector n) :
    Continuous (fun A : Herm n => ellipsoidQuadratic A η) := by
  unfold ellipsoidQuadratic Matrix.mulVec dotProduct
  fun_prop

theorem posSemidef_iff_ellipsoidQuadratic_nonneg (A : Herm n) :
    A.PosSemidef ↔ A.IsHermitian ∧ ∀ η : ComplexVector n,
      0 ≤ ellipsoidQuadratic A η := by
  constructor
  · intro hA
    exact ⟨hA.isHermitian, ellipsoidQuadratic_nonneg hA⟩
  · rintro ⟨hA, hq⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
    intro u
    apply Complex.nonneg_iff.mpr
    exact ⟨hq (WithLp.toLp 2 u), (hA.im_star_dotProduct_mulVec_self u).symm⟩

theorem isClosed_hermitian_matrices :
    IsClosed {A : Herm n | A.IsHermitian} := by
  change IsClosed {A : Herm n | Aᴴ = A}
  exact isClosed_eq (by fun_prop) continuous_id

theorem isClosed_posSemidef_matrices :
    IsClosed {A : Herm n | A.PosSemidef} := by
  have heq : {A : Herm n | A.PosSemidef} =
      {A : Herm n | A.IsHermitian} ∩
        ⋂ η : ComplexVector n, {A : Herm n | 0 ≤ ellipsoidQuadratic A η} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      posSemidef_iff_ellipsoidQuadratic_nonneg]
  rw [heq]
  exact isClosed_hermitian_matrices.inter
    (isClosed_iInter fun η => isClosed_le continuous_const (continuous_ellipsoidQuadratic η))

theorem isClosed_quadratic_minorants (v : ComplexVector n → EReal) :
    IsClosed {A : Herm n | ∀ η : ComplexVector n,
      (ellipsoidQuadratic A η : EReal) ≤ v η} := by
  have heq : {A : Herm n | ∀ η : ComplexVector n,
      (ellipsoidQuadratic A η : EReal) ≤ v η} =
      ⋂ η : ComplexVector n, {A : Herm n | (ellipsoidQuadratic A η : EReal) ≤ v η} := by
    ext A
    simp
  rw [heq]
  exact isClosed_iInter fun η =>
    isClosed_le (continuous_coe_real_ereal.comp (continuous_ellipsoidQuadratic η)) continuous_const

theorem isClosed_psd_minorants (v : ComplexVector n → EReal) :
    IsClosed {A : Herm n | A.PosSemidef ∧ ∀ η : ComplexVector n,
      (ellipsoidQuadratic A η : EReal) ≤ v η} :=
  isClosed_posSemidef_matrices.inter (isClosed_quadratic_minorants v)

end Yau.NodeProofs.E01Aux
