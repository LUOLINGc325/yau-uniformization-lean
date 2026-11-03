import Yau.Proofs.F01MatrixBarJet
import Yau.Proofs.F01KahlerMixedExchange
import Yau.LeafProofs.L12

/-! Differentiating the actual inverse-matrix identity gives the barred
inverse jet; no extra matrix derivative is supplied by the caller. -/
noncomputable section
open Set Filter
open scoped Matrix ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem matrixBarJet_inverse (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    {S : Set (ComplexVector n)} (hS : IsOpen S)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun w => H w i j) S)
    (hdet : ∀ w ∈ S, (H w).det ≠ 0) {z : ComplexVector n} (hz : z ∈ S) (v : ComplexVector n) :
    matrixBarJet (fun w => (H w)⁻¹) z v =
      -((H z)⁻¹ * matrixBarJet H z v * (H z)⁻¹) := by
  have hHd (i j : Fin n) := ((hH i j).contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hId (i j : Fin n) := ((L12Aux.contDiffOn_matrix_inv hH hdet i j).contDiffAt
    (hS.mem_nhds hz)).differentiableAt (by simp)
  have hzero : matrixBarJet (fun w => H w * (H w)⁻¹) z v = 0 := by
    ext i j
    have hgerm : (fun w => (H w * (H w)⁻¹) i j) =ᶠ[𝓝 z]
        (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j) := by
      filter_upwards [hS.mem_nhds hz] with w hw
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet w hw))]
    change wirtBar _ z v = 0
    rw [wirtBar_eq_of_eventuallyEq hgerm]
    simp [wirtBar]
  have hh := matrixBarJet_mul H (fun w => (H w)⁻¹) z v hHd hId
  rw [hzero] at hh
  have hc := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (H z)⁻¹ * A) hh.symm
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet z hz)), Matrix.one_mul, Matrix.mul_zero] at hc
  calc
    matrixBarJet (fun w => (H w)⁻¹) z v =
        -((H z)⁻¹ * matrixBarJet H z v * (H z)⁻¹) +
          ((H z)⁻¹ * matrixBarJet H z v * (H z)⁻¹ + matrixBarJet (fun w => (H w)⁻¹) z v) := by abel
    _ = _ := by rw [hc, add_zero]

end Yau.NodeProofs.F01Aux
