import Yau.Proofs.C04NormalEllipticModelBasis
import Yau.LeafProofs.L21LocalChart
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual inverse-Gram coefficient formula has one uniform ellipticity
constant on the fixed operator neighborhood. No dimension lower bound is used. -/

noncomputable section
open scoped Topology InnerProductSpace

namespace Yau.Proofs.C04Aux
open Yau Yau.LeafProofs.L21Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {n : ℕ}

def normalEllipticPrincipal (B : ComplexVector n →L[ℝ] ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  fun i j => (1 / 2 : ℝ) * ∑ c : RIdx n,
    realCoord (B (realVec c)) i * realCoord (B (realVec c)) j

theorem normalEllipticPrincipal_isSymm (B : ComplexVector n →L[ℝ] ComplexVector n) :
    (normalEllipticPrincipal B).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, normalEllipticPrincipal]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  exact mul_comm _ _

theorem normalEllipticPrincipal_quadratic
    (B : ComplexVector n →L[ℝ] ComplexVector n) (v : RIdx n → ℝ) :
    let V := (normalEllipticRealBasis n).repr.symm (WithLp.toLp 2 v)
    ∑ i, ∑ j, normalEllipticPrincipal B i j * v i * v j =
      (1 / 2 : ℝ) * ‖B.adjoint V‖ ^ 2 := by
  dsimp only
  let V := (normalEllipticRealBasis n).repr.symm (WithLp.toLp 2 v)
  have hvexp : V = ∑ i : RIdx n, v i • realVec i := by
    simpa only [V, LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply,
      normalEllipticRealBasis_apply] using ((normalEllipticRealBasis n).sum_repr V).symm
  have hlinear (c : RIdx n) :
      ∑ i : RIdx n, realCoord (B (realVec c)) i * v i =
        realCoord (B.adjoint V) c := by
    rw [normal_elliptic_realCoord_inner, ContinuousLinearMap.adjoint_inner_right, hvexp,
      inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_smul_right, real_inner_comm, ← normal_elliptic_realCoord_inner]
    ring
  calc
    ∑ i, ∑ j, normalEllipticPrincipal B i j * v i * v j =
        ∑ i, ∑ j, ∑ c : RIdx n,
          (1 / 2 : ℝ) * (realCoord (B (realVec c)) i * v i) *
            (realCoord (B (realVec c)) j * v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [normalEllipticPrincipal, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = ∑ i, ∑ c : RIdx n, ∑ j,
          (1 / 2 : ℝ) * (realCoord (B (realVec c)) i * v i) *
            (realCoord (B (realVec c)) j * v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ c : RIdx n, ∑ i, ∑ j,
          (1 / 2 : ℝ) * (realCoord (B (realVec c)) i * v i) *
            (realCoord (B (realVec c)) j * v j) := Finset.sum_comm
    _ = (1 / 2 : ℝ) * ∑ c : RIdx n,
          (∑ i : RIdx n, realCoord (B (realVec c)) i * v i) ^ 2 := by
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (1 / 2 : ℝ) * ‖B.adjoint V‖ ^ 2 := by
      rw [normal_elliptic_norm_sq]
      simp_rw [hlinear]

theorem normal_elliptic_principal_ellipticity
    (A : ComplexVector n →L[ℝ] ComplexVector n)
    (hnear : ‖A - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ)) :
    (normalEllipticPrincipal A.inverse).IsSymm ∧ ∀ v : RIdx n → ℝ,
      (1 / 8 : ℝ) * ∑ i, (v i) ^ 2 ≤
        ∑ i, ∑ j, normalEllipticPrincipal A.inverse i j * v i * v j := by
  refine ⟨normalEllipticPrincipal_isSymm _, ?_⟩
  intro v
  let V := (normalEllipticRealBasis n).repr.symm (WithLp.toLp 2 v)
  have hVcoord (i : RIdx n) : realCoord V i = v i := by
    rw [← normalEllipticRealBasis_repr]
    simp [V]
  have hVnorm : ‖V‖ ^ 2 = ∑ i : RIdx n, (v i) ^ 2 := by
    rw [normal_elliptic_norm_sq]
    simp_rw [hVcoord]
  have hInv := isInvertible_of_norm_sub_id_lt_one A (hnear.trans_lt (by norm_num))
  have hAnorm : ‖A‖ ≤ 2 := by
    calc
      ‖A‖ = ‖(A - ContinuousLinearMap.id ℝ (ComplexVector n)) +
          ContinuousLinearMap.id ℝ (ComplexVector n)‖ := by congr 1; abel
      _ ≤ ‖A - ContinuousLinearMap.id ℝ (ComplexVector n)‖ +
          ‖ContinuousLinearMap.id ℝ (ComplexVector n)‖ := norm_add_le _ _
      _ ≤ (1 / 4 : ℝ) + 1 := add_le_add hnear ContinuousLinearMap.norm_id_le
      _ ≤ 2 := by norm_num
  have hAnormAdj : ‖A.adjoint‖ ≤ 2 := by
    simpa only [LinearIsometryEquiv.norm_map] using hAnorm
  have hAdj : A.adjoint.comp (A.inverse.adjoint) =
      ContinuousLinearMap.id ℝ (ComplexVector n) := by
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg (fun T : ComplexVector n →L[ℝ] ComplexVector n => T.adjoint)
        hInv.inverse_comp_self
  have hAdjV : A.adjoint (A.inverse.adjoint V) = V := by
    exact congrArg (fun T : ComplexVector n →L[ℝ] ComplexVector n => T V) hAdj
  have hnorm : ‖V‖ ≤ 2 * ‖A.inverse.adjoint V‖ := by
    calc
      ‖V‖ = ‖A.adjoint (A.inverse.adjoint V)‖ := congrArg norm hAdjV.symm
      _ ≤ ‖A.adjoint‖ * ‖A.inverse.adjoint V‖ := A.adjoint.le_opNorm _
      _ ≤ 2 * ‖A.inverse.adjoint V‖ :=
        mul_le_mul_of_nonneg_right hAnormAdj (norm_nonneg _)
  have hsquare := (sq_le_sq₀ (norm_nonneg V)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _))).2 hnorm
  rw [normalEllipticPrincipal_quadratic]
  change (1 / 8 : ℝ) * ∑ i, (v i) ^ 2 ≤ (1 / 2 : ℝ) * ‖A.inverse.adjoint V‖ ^ 2
  rw [← hVnorm]
  nlinarith

end Yau.Proofs.C04Aux
