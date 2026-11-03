import Yau.Proofs.F01WirtingerMatrixCongruence
import Yau.Proofs.F01WirtingerLinear
import Yau.Proofs.F01AffineCoordinate

/-! The actual holomorphic first-jet symmetry survives a constant complex
change of coordinates and its matching congruence of the metric. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem affine_congruence_wirt_symmetry
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) (z0 z : ComplexVector n)
    (hG : ∀ p q, DifferentiableAt ℝ (fun y => G y p q)
      (affineCoordinateHomeomorph z0 A hA z))
    (hsym : ∀ p q l,
      wirt (fun y => G y p q) (affineCoordinateHomeomorph z0 A hA z) (stdVec l) =
      wirt (fun y => G y p l) (affineCoordinateHomeomorph z0 A hA z) (stdVec q))
    (i j k : Fin n) :
    wirt (fun w => (Aᴴ * G (affineCoordinateHomeomorph z0 A hA w) * A) i j) z (stdVec k) =
      wirt (fun w => (Aᴴ * G (affineCoordinateHomeomorph z0 A hA w) * A) i k) z (stdVec j) := by
  have hT := (affineCoordinateHomeomorph_contDiff z0 A hA).differentiable (by simp) z
  have hcoord (l b : Fin n) : matrixCoordinateEquiv A hA (stdVec b) l = A l b :=
    congrArg (fun D : Matrix (Fin n) (Fin n) ℂ => D l b) (matrixCoordinateEquiv_native_matrix A hA)
  have hjet (p q b : Fin n) :
      wirt (fun y => G y p q) (affineCoordinateHomeomorph z0 A hA z)
        (matrixCoordinateEquiv A hA (stdVec b)) =
      ∑ l, wirt (fun y => G y p q) (affineCoordinateHomeomorph z0 A hA z) (stdVec l) * A l b := by
    rw [wirt_eq_coordinate_contraction]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro l hl
    rw [hcoord]
  have hentry (a b : Fin n) := wirt_matrix_congruence_entry A G
    (affineCoordinateHomeomorph z0 A hA) z (stdVec b) hT hG i a
  simp only [(affineCoordinateHomeomorph_hasFDerivAt z0 A hA z).fderiv,
    ContinuousLinearEquiv.coe_coe] at hentry
  simp_rw [hjet] at hentry
  rw [hentry j k, hentry k j]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro l hl
  rw [hsym p l q]
  ring

end Yau.NodeProofs.F01Aux
