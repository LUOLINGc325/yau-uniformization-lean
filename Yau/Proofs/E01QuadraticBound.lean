import Yau.Proofs.E01QuadraticFiber

/-! A dimension-free operator bound and genuine positive matrix line variations. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem abs_ellipsoidQuadratic_le_opNorm (A : Herm n) (η : ComplexVector n) :
    |ellipsoidQuadratic A η| ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ * ‖η‖ ^ 2 := by
  have heq : star (WithLp.ofLp η) ⬝ᵥ (A *ᵥ WithLp.ofLp η) =
      inner ℂ η (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A η) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  calc
    |ellipsoidQuadratic A η| ≤ ‖star (WithLp.ofLp η) ⬝ᵥ (A *ᵥ WithLp.ofLp η)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖inner ℂ η (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A η)‖ := congrArg norm heq
    _ ≤ ‖η‖ * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A η‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖ * (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).le_opNorm η) (norm_nonneg η)
    _ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ * ‖η‖ ^ 2 := by ring

theorem one_add_matrix_line_posDef
    (H : Herm n) (hH : H.IsHermitian) {s : ℝ} (hs : 0 ≤ s)
    (hsmall : s * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H‖ < 1) :
    (1 + (s : ℂ) • H).PosDef := by
  have hHerm : (1 + (s : ℂ) • H).IsHermitian := by
    unfold Matrix.IsHermitian
    simp [hH.eq]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro u hu
  have hη : (WithLp.toLp 2 u : ComplexVector n) ≠ 0 := by
    intro hz
    apply hu
    ext i
    exact congrArg (fun η : ComplexVector n => η i) hz
  apply Complex.pos_iff.mpr
  refine ⟨?_, (hHerm.im_star_dotProduct_mulVec_self u).symm⟩
  change 0 < ellipsoidQuadratic (1 + (s : ℂ) • H) (WithLp.toLp 2 u)
  rw [ellipsoidQuadratic_add, ellipsoidQuadratic_one, ellipsoidQuadratic_real_smul]
  have hnorm : 0 < ‖(WithLp.toLp 2 u : ComplexVector n)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hη)
  have hlow := (abs_le.mp (abs_ellipsoidQuadratic_le_opNorm H (WithLp.toLp 2 u))).1
  calc
    0 < (1 - s * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H‖) * ‖(WithLp.toLp 2 u : ComplexVector n)‖ ^ 2 :=
      mul_pos (sub_pos.mpr hsmall) hnorm
    _ = ‖(WithLp.toLp 2 u : ComplexVector n)‖ ^ 2 +
        s * (-(‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H‖ * ‖(WithLp.toLp 2 u : ComplexVector n)‖ ^ 2)) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlow hs)

end Yau.NodeProofs.E01Aux
