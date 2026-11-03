import Yau.Proofs.E02MatrixBasic
import Yau.Proofs.V05Matrix

open Matrix Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem schurComplement_isHermitian {n : ℕ}
    (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hW : W.IsHermitian) (hC : W.toBlocks₂₂.PosDef) :
    (schurComplement W).IsHermitian := by
  let := hC.isUnit.invertible
  exact (Matrix.IsHermitian.fromBlocks₂₂ _ _ hC.isHermitian).mp
    (V05Aux.hermitian_blocks hW ▸ hW)

/-- Continuity at the actual positive vertical block, in the fixed finite
matrix topology. No continuity of chosen Peano tensors is required. -/
theorem schurComplement_continuousAt {n : ℕ}
    (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hC : W.toBlocks₂₂.PosDef) : ContinuousAt (schurComplement (n := n)) W := by
  have h11 : Continuous (fun B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ => B.toBlocks₁₁) :=
    continuous_id.matrix_submatrix Sum.inl Sum.inl
  have h12 : Continuous (fun B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ => B.toBlocks₁₂) :=
    continuous_id.matrix_submatrix Sum.inl Sum.inr
  have h22 : Continuous (fun B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ => B.toBlocks₂₂) :=
    continuous_id.matrix_submatrix Sum.inr Sum.inr
  have hInv : ContinuousAt (fun C : Herm n => C⁻¹) W.toBlocks₂₂ :=
    continuousAt_matrix_inv W.toBlocks₂₂ (by
      simpa only [Ring.inverse_eq_inv'] using
        (continuousAt_inv₀ (ne_of_gt hC.det_pos) :
          ContinuousAt (fun z : ℂ => z⁻¹) W.toBlocks₂₂.det))
  exact h11.continuousAt.sub
    ((h12.continuousAt.mul (hInv.comp h22.continuousAt)).mul
      h12.matrix_conjTranspose.continuousAt)

end Yau.NodeProofs.E02Aux
