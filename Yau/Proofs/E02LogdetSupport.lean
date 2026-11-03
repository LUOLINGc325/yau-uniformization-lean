import Yau.Proofs.E02SpectralLogdet
import Yau.Proofs.G04Whitening

open Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- One fixed Hermitian whitening relates the actual product determinant
and trace to a single positive matrix. No eigenbasis varies with parameters. -/
theorem logdet_whiten_product {n : ℕ} (A B : Herm n) (hA : A.PosDef) (hB : B.PosDef) :
    ∃ C : Herm n, C.PosDef ∧
      Real.log C.det.re = Real.log A.det.re+Real.log B.det.re ∧
      (Matrix.trace C).re = (Matrix.trace (B*A)).re ∧
      (C = 1 ↔ A = B⁻¹) := by
  obtain ⟨S,hS,hu,hSS,hSBS⟩ := G04Aux.exists_hermitian_whitening B⁻¹ hB.inv
  have hSSB : S*S = B := hSS.trans
    (Matrix.nonsing_inv_nonsing_inv _ (hB.isUnit.map Matrix.detMonoidHom))
  let C := S*A*S
  have hC : C.PosDef := by
    have hp := hA.conjTranspose_mul_mul_same (B := S) (Matrix.mulVec_injective_of_isUnit hu)
    simpa only [hS.eq] using hp
  have hAr : 0 < A.det.re := (RCLike.pos_iff.mp hA.det_pos).1
  have hAi : A.det.im = 0 := (RCLike.pos_iff.mp hA.det_pos).2
  have hBr : 0 < B.det.re := (RCLike.pos_iff.mp hB.det_pos).1
  have hBi : B.det.im = 0 := (RCLike.pos_iff.mp hB.det_pos).2
  have hDet : C.det = A.det*B.det := by
    change (S*A*S).det = _
    rw [Matrix.det_mul,Matrix.det_mul,←hSSB,Matrix.det_mul]
    ring
  have hLog : Real.log C.det.re = Real.log A.det.re+Real.log B.det.re := by
    rw [hDet]
    simp only [Complex.mul_re,hAi,hBi,mul_zero,sub_zero]
    exact Real.log_mul hAr.ne' hBr.ne'
  have hTrace : (Matrix.trace C).re = (Matrix.trace (B*A)).re := by
    change (Matrix.trace (S*A*S)).re = _
    rw [Matrix.trace_mul_cycle,hSSB]
  refine ⟨C,hC,hLog,hTrace,?_⟩
  constructor
  · intro hC1
    apply hu.mul_left_cancel
    apply hu.mul_right_cancel
    exact hC1.trans hSBS.symm
  · rintro rfl
    exact hSBS

theorem trace_logdet_support {n : ℕ} (A B : Herm n) (hA : A.PosDef) (hB : B.PosDef) :
    (n:ℝ)+Real.log A.det.re+Real.log B.det.re ≤ (Matrix.trace (B*A)).re := by
  obtain ⟨C,hC,hLog,hTrace,_⟩ := logdet_whiten_product A B hA hB
  have hLe := logdet_le_trace_sub_dim C hC
  rw [hLog,hTrace] at hLe
  simpa only [add_assoc] using hLe

theorem trace_logdet_support_eq_iff {n : ℕ} (A B : Herm n) (hA : A.PosDef) (hB : B.PosDef) :
    ((n:ℝ)+Real.log A.det.re+Real.log B.det.re = (Matrix.trace (B*A)).re) ↔ A = B⁻¹ := by
  obtain ⟨C,hC,hLog,hTrace,hEq⟩ := logdet_whiten_product A B hA hB
  have hIff := logdet_eq_trace_sub_dim_iff C hC
  rw [hLog,hTrace] at hIff
  simpa only [add_assoc] using hIff.trans hEq

end Yau.NodeProofs.E02Aux
