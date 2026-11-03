import Mathlib

/-! Matrix inequalities for the symplectic Schur-complement lemma. -/

noncomputable section

namespace Yau.NodeProofs.V05Aux

open Matrix
open scoped Matrix ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  obtain ⟨F, hF⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hF, star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact (hA.mul_mul_conjTranspose_same F).trace_nonneg

omit [Fintype ι] [DecidableEq ι] in
/-- The two off-diagonal blocks of a Hermitian block matrix are adjoints. -/
theorem hermitian_blocks {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ} (hH : H.IsHermitian) :
    fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₁₂ᴴ H.toBlocks₂₂ = H := by
  have hc : H.toBlocks₁₂ᴴ = H.toBlocks₂₁ := by
    ext i j
    exact hH.apply (Sum.inr i) (Sum.inl j)
  rw [hc, Matrix.fromBlocks_toBlocks]

/-- Completing the square gives the Schur form plus a nonnegative vertical square. -/
theorem schur_minimum {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hH : H.IsHermitian) (hD : H.toBlocks₂₂.PosDef) (x y : ι → ℂ) :
    star x ⬝ᵥ ((H.toBlocks₁₁ - H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ) *ᵥ x) ≤
      star (x ⊕ᵥ y) ⬝ᵥ (H *ᵥ (x ⊕ᵥ y)) := by
  let := hD.isUnit.invertible
  have hid := Matrix.schur_complement_eq₂₂ H.toBlocks₁₁ H.toBlocks₁₂ x y hD.isHermitian
  simp only [hermitian_blocks hH, ← Matrix.dotProduct_mulVec] at hid
  rw [hid]
  exact le_add_of_nonneg_left (hD.posSemidef.dotProduct_mulVec_nonneg _)

/-- The minimizing vertical vector realizes the Schur complement. -/
theorem schur_at_minimizer {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hH : H.IsHermitian) (hD : H.toBlocks₂₂.PosDef) (x : ι → ℂ) :
    star (x ⊕ᵥ -((H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ) *ᵥ x)) ⬝ᵥ
      (H *ᵥ (x ⊕ᵥ -((H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ) *ᵥ x))) =
      star x ⬝ᵥ ((H.toBlocks₁₁ - H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ) *ᵥ x) := by
  let := hD.isUnit.invertible
  have hid := Matrix.schur_complement_eq₂₂ H.toBlocks₁₁ H.toBlocks₁₂ x
    (-((H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ) *ᵥ x)) hD.isHermitian
  simpa only [hermitian_blocks hH, ← Matrix.dotProduct_mulVec, add_neg_cancel,
    star_zero, dotProduct_zero, zero_add] using hid

/-- The Schur complement of a positive matrix is positive semidefinite. -/
theorem schur_posSemidef {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ} (hH : H.PosDef) :
    (H.toBlocks₁₁ - H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ).PosSemidef := by
  have hD : H.toBlocks₂₂.PosDef := hH.submatrix Sum.inr_injective
  let := hD.isUnit.invertible
  exact (Matrix.PosDef.fromBlocks₂₂ _ _ hD).mp
    (hermitian_blocks hH.isHermitian ▸ hH.posSemidef)

/-- Schur complementation preserves the order when both vertical blocks are positive. -/
theorem schur_mono {H W : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ}
    (hH : H.PosDef) (hW : W.IsHermitian) (hHW : (H - W).PosSemidef)
    (hC : W.toBlocks₂₂.PosDef) :
    ((H.toBlocks₁₁ - H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ) -
      (W.toBlocks₁₁ - W.toBlocks₁₂ * W.toBlocks₂₂⁻¹ * W.toBlocks₁₂ᴴ)).PosSemidef := by
  have hD : H.toBlocks₂₂.PosDef := hH.submatrix Sum.inr_injective
  have hSW : (W.toBlocks₁₁ - W.toBlocks₁₂ * W.toBlocks₂₂⁻¹ * W.toBlocks₁₂ᴴ).IsHermitian := by
    let := hC.isUnit.invertible
    exact (Matrix.IsHermitian.fromBlocks₂₂ _ _ hC.isHermitian).mp
      (hermitian_blocks hW ▸ hW)
  refine .of_dotProduct_mulVec_nonneg ((schur_posSemidef hH).isHermitian.sub hSW) fun x => ?_
  let y := -((H.toBlocks₂₂⁻¹ * H.toBlocks₁₂ᴴ) *ᵥ x)
  have hord : star (x ⊕ᵥ y) ⬝ᵥ (W *ᵥ (x ⊕ᵥ y)) ≤
      star (x ⊕ᵥ y) ⬝ᵥ (H *ᵥ (x ⊕ᵥ y)) := by
    exact sub_nonneg.mp (by
      simpa only [Matrix.sub_mulVec, dotProduct_sub] using
        hHW.dotProduct_mulVec_nonneg (x ⊕ᵥ y))
  have hm := (schur_minimum hW hC x y).trans hord
  rw [schur_at_minimizer hH.isHermitian hD] at hm
  simpa only [Matrix.sub_mulVec, dotProduct_sub] using sub_nonneg.mpr hm

end Yau.NodeProofs.V05Aux

namespace Yau.NodeProofs.V05Aux

open Matrix
open scoped Matrix ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The vertical contribution in the shear is an antisymmetric square. -/
theorem antisymmetric_trace (D R : Matrix ι ι ℂ) :
    ((R - Rᵀ)ᴴ * D * (R - Rᵀ) * Dᵀ).trace =
      2 * ((Rᴴ * D * R * Dᵀ).trace - (Rᴴ * D * Rᵀ * Dᵀ).trace) := by
  have hRt : (Rᵀ)ᴴᵀ = Rᴴ := rfl
  have hself : ((Rᵀ)ᴴ * D * Rᵀ * Dᵀ).trace = (Rᴴ * D * R * Dᵀ).trace := by
    rw [← Matrix.trace_transpose]
    simp only [transpose_mul, transpose_transpose, hRt]
    simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_comm (D * R * Dᵀ) Rᴴ)
  have hcross : ((Rᵀ)ᴴ * D * R * Dᵀ).trace = (Rᴴ * D * Rᵀ * Dᵀ).trace := by
    rw [← Matrix.trace_transpose]
    simp only [transpose_mul, transpose_transpose, hRt]
    simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_comm (D * Rᵀ * Dᵀ) Rᴴ)
  simp only [conjTranspose_sub, sub_mul, mul_sub, Matrix.trace_sub]
  rw [hself, hcross]
  ring

/-- Nonnegativity of the vertical exterior-square contribution. -/
theorem vertical_cost_nonneg {D : Matrix ι ι ℂ} (hD : D.PosDef)
    (B : Matrix ι ι ℂ) :
    0 ≤ ((Dᵀ * (B * D⁻¹ * Bᴴ)).trace - (B * (Bᴴ)ᵀ).trace).re := by
  let := hD.isUnit.invertible
  let R := D⁻¹ * Bᴴ
  have hDR : D * R = Bᴴ := by simp [R, ← Matrix.mul_assoc]
  have hRD : Rᴴ * D = B := by
    have h := congrArg Matrix.conjTranspose hDR
    simpa only [conjTranspose_mul, hD.isHermitian.eq, conjTranspose_conjTranspose] using h
  have ht : (Rᴴ * D * R * Dᵀ).trace = (Dᵀ * (B * D⁻¹ * Bᴴ)).trace := by
    rw [hRD, Matrix.trace_mul_comm]
    simp only [R, Matrix.mul_assoc]
  have hb : (Rᴴ * D * Rᵀ * Dᵀ).trace = (B * (Bᴴ)ᵀ).trace := by
    rw [hRD, Matrix.mul_assoc, ← transpose_mul, hDR]
  have hpos := trace_mul_nonneg
    (hD.posSemidef.conjTranspose_mul_mul_same (R - Rᵀ)) hD.posSemidef.transpose
  rw [antisymmetric_trace, ht, hb] at hpos
  have hposR := (RCLike.nonneg_iff.mp hpos).1
  norm_num [Complex.mul_re] at hposR
  simpa only [Complex.sub_re, sub_nonneg] using hposR

end Yau.NodeProofs.V05Aux
