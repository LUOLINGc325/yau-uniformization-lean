import Yau.Proofs.V01TraceCompact

/-! V01 scratch source: continuity is used only where the vertical block is
invertible; no continuity of total matrix inversion at singular blocks. -/

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

theorem continuous_toBlocks₁₁ :
    Continuous (fun W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ => W.toBlocks₁₁) :=
  continuous_id.matrix_submatrix Sum.inl Sum.inl

theorem continuous_toBlocks₁₂ :
    Continuous (fun W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ => W.toBlocks₁₂) :=
  continuous_id.matrix_submatrix Sum.inl Sum.inr

theorem continuous_toBlocks₂₂ :
    Continuous (fun W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ => W.toBlocks₂₂) :=
  continuous_id.matrix_submatrix Sum.inr Sum.inr

theorem continuousAt_schurComplement
    {W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hC : W.toBlocks₂₂.PosDef) : ContinuousAt schurComplement W := by
  have hInv : ContinuousAt (Inv.inv : Herm n → Herm n) W.toBlocks₂₂ :=
    continuousAt_matrix_inv W.toBlocks₂₂ (by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hC.det_pos.ne')
  exact continuous_toBlocks₁₁.continuousAt.sub
    ((continuous_toBlocks₁₂.continuousAt.mul
      (hInv.comp continuous_toBlocks₂₂.continuousAt)).mul
        continuous_toBlocks₁₂.matrix_conjTranspose.continuousAt)

theorem tendsto_schurComplement
    {W : ℕ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    {W₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hW : Tendsto W atTop (𝓝 W₀)) (hC : W₀.toBlocks₂₂.PosDef) :
    Tendsto (fun m => schurComplement (W m)) atTop (𝓝 (schurComplement W₀)) :=
  (continuousAt_schurComplement hC).tendsto.comp hW

end Yau.Blueprint.V01Proof
