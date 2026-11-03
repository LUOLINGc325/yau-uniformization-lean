import Yau.Proofs.V05Matrix
import spec.CHAIN.CONTRACTS

/-! The paper's symplectic Schur-complement inequality, including the
nonnegative vertical contribution of a general shear. -/

noncomputable section

namespace Yau.NodeProofs

open Yau Yau.Blueprint Matrix
open scoped Matrix ComplexOrder

/-- The all-dimensional symplectic Schur-complement lemma. -/
theorem V05_proved : Yau.Blueprint.V05 := by
  intro n H W hH hW hHW hC
  have hD : H.toBlocks₂₂.PosDef := hH.submatrix Sum.inr_injective
  have hS : (schurComplement H).PosSemidef := V05Aux.schur_posSemidef hH
  refine ⟨hS, V05Aux.schur_mono hH hW hHW hC, ?_⟩
  have hDC : (H.toBlocks₂₂ - W.toBlocks₂₂).PosSemidef := hHW.submatrix Sum.inr
  have htr := V05Aux.trace_mul_nonneg hDC.transpose hS
  have htrR : 0 ≤ (((H.toBlocks₂₂ - W.toBlocks₂₂)ᵀ * schurComplement H).trace).re :=
    (RCLike.nonneg_iff.mp htr).1
  have hvert := V05Aux.vertical_cost_nonneg hD H.toBlocks₁₂
  have hvertR := hvert
  have hsum : (∑ i, ∑ j, H.toBlocks₁₂ i j * star (H.toBlocks₁₂ j i)) =
      (H.toBlocks₁₂ * (H.toBlocks₁₂ᴴ)ᵀ).trace := by
    rfl
  simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.trace_sub,
    Complex.sub_re] at htrR
  simp only [Complex.sub_re] at hvertR
  unfold symplecticP
  rw [hsum, Complex.sub_re, Matrix.trace_mul_comm H.toBlocks₁₁]
  have hsplit : (H.toBlocks₂₂ᵀ * schurComplement H).trace =
      (H.toBlocks₂₂ᵀ * H.toBlocks₁₁).trace -
        (H.toBlocks₂₂ᵀ * (H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ)).trace := by
    simp only [schurComplement, Matrix.mul_sub, Matrix.trace_sub]
  have hsplitR := congrArg Complex.re hsplit
  simp only [Complex.sub_re] at hsplitR
  linarith

/-- The frozen V05 contract, without any additional premise. -/
theorem V05_contract_proved : Yau.BlueprintContracts.V05_contract := V05_proved

end Yau.NodeProofs
