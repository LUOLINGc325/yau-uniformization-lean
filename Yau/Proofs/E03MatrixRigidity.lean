import Yau.Proofs.E01FeasibleCompact
import Yau.Proofs.E01CometricDet
import Yau.Proofs.E02LogdetSupport
import Yau.Proofs.V05Matrix

/-! SOURCE-ONLY E03 candidate. No receiver or Lean invocation has checked this file. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem trace_inv_mul_le_dim_of_psd_order (B C : Herm n) (hC : C.PosDef)
    (hle : (C - B).PosSemidef) : (Matrix.trace (C⁻¹ * B)).re ≤ n := by
  have hn : 0 ≤ (Matrix.trace (C⁻¹ * (C - B))).re :=
    (Complex.nonneg_iff.mp (V05Aux.trace_mul_nonneg hC.inv.posSemidef hle)).1
  rw [Matrix.mul_sub, Matrix.trace_sub,
    Matrix.nonsing_inv_mul _ (hC.isUnit.map Matrix.detMonoidHom)] at hn
  have ht : (Matrix.trace (1 : Herm n)).re = (n : ℝ) := by simp
  rw [Complex.sub_re, ht] at hn
  linarith

theorem eq_of_posDef_order_logdet_eq (B C : Herm n) (hB : B.PosDef) (hC : C.PosDef)
    (hle : (C - B).PosSemidef)
    (hdet : Real.log B.det.re = Real.log C.det.re) : B = C := by
  have hupper := trace_inv_mul_le_dim_of_psd_order B C hC hle
  have hlower := E02Aux.trace_logdet_support B C⁻¹ hB hC.inv
  have hv : (n : ℝ) + Real.log B.det.re + Real.log (C⁻¹).det.re = n := by
    rw [hdet, E01Aux.logdet_inverse_posDef C hC]
    ring
  have heq : (n : ℝ) + Real.log B.det.re + Real.log (C⁻¹).det.re =
      (Matrix.trace (C⁻¹ * B)).re := by linarith
  have hBC := (E02Aux.trace_logdet_support_eq_iff B C⁻¹ hB hC.inv).mp heq
  exact hBC.trans (Matrix.nonsing_inv_nonsing_inv _ (hC.isUnit.map Matrix.detMonoidHom))

end Yau.NodeProofs.E03Aux
