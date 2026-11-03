import Yau.Proofs.F01InverseBarJet
import Yau.LeafProofs.L14Gauge

/-! The original metric-lowered Chern curvature equals the actual second
matrix jet and its quadratic first-jet term. -/
noncomputable section
open Set Filter
open scoped Matrix ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem curvatureMatrix_eq_actual_jets (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    {S : Set (ComplexVector n)} (hS : IsOpen S)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun w => H w i j) S)
    (hdet : ∀ w ∈ S, (H w).det ≠ 0) {z : ComplexVector n} (hz : z ∈ S) (i j : Fin n) :
    BundleDbar.curvatureMatrix H z i j =
      matrixBarJet H z (stdVec j) * (H z)⁻¹ * matrixUnbarJet H z (stdVec i) -
        matrixBarJet (fun w => matrixUnbarJet H w (stdVec i)) z (stdVec j) := by
  have hId (a b : Fin n) := ((L12Aux.contDiffOn_matrix_inv hH hdet a b).contDiffAt
    (hS.mem_nhds hz)).differentiableAt (by simp)
  have hDd (a b : Fin n) : DifferentiableAt ℝ
      (fun w => matrixUnbarJet H w (stdVec i) a b) z :=
    ((L14Aux.wirt_contDiffOn hS _ (hH a b) (stdVec i)).contDiffAt
      (hS.mem_nhds hz)).differentiableAt (by simp)
  change -(H z * matrixBarJet (fun w => (H w)⁻¹ * matrixUnbarJet H w (stdVec i))
    z (stdVec j)) = _
  rw [matrixBarJet_mul _ _ z (stdVec j) hId hDd,
    matrixBarJet_inverse H hS hH hdet hz (stdVec j)]
  have hcancel : H z * (H z)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet z hz))
  calc
    _ = (H z * (H z)⁻¹) *
        (matrixBarJet H z (stdVec j) * (H z)⁻¹ * matrixUnbarJet H z (stdVec i) -
          matrixBarJet (fun w => matrixUnbarJet H w (stdVec i)) z (stdVec j)) := by noncomm_ring
    _ = _ := by rw [hcancel, Matrix.one_mul]

theorem curvatureMatrix_at_zero_first_jet (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    {S : Set (ComplexVector n)} (hS : IsOpen S)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun w => H w i j) S)
    (hdet : ∀ w ∈ S, (H w).det ≠ 0) {z : ComplexVector n} (hz : z ∈ S)
    (hzero : ∀ a b, fderiv ℝ (fun w => H w a b) z = 0) (i j a b : Fin n) :
    BundleDbar.curvatureMatrix H z i j a b =
      -wirt (fun w => wirtBar (fun y => H y a b) w (stdVec j)) z (stdVec i) := by
  have hU : matrixUnbarJet H z (stdVec i) = 0 := by
    ext a b
    simp only [matrixUnbarJet, wirt, hzero a b, ContinuousLinearMap.zero_apply,
      mul_zero, sub_self, Matrix.zero_apply]
  rw [curvatureMatrix_eq_actual_jets H hS hH hdet hz i j, hU, Matrix.mul_zero,
    zero_sub]
  change -wirtBar (fun w => wirt (fun y => H y a b) w (stdVec i)) z (stdVec j) = _
  have htwice : ContDiffAt ℝ 2 (fun w => H w a b) z :=
    ((hH a b).contDiffAt (hS.mem_nhds hz)).of_le (by simp)
  rw [← L14Aux.wirt_wirtBar_comm _ z htwice (stdVec j) (stdVec i)]

end Yau.NodeProofs.F01Aux
