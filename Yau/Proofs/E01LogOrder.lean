import Yau.Proofs.E01CometricDet
import Yau.Proofs.E01FeasibleCompact
import Yau.Proofs.E02LogdetSupport
import Yau.Proofs.V05Matrix

/-! Actual log-determinant order from the shared trace-logdet support theorem. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem logdet_mono_posDef (A B : Herm n) (hA : A.PosDef) (hB : B.PosDef)
    (hle : (B - A).PosSemidef) : Real.log A.det.re ≤ Real.log B.det.re := by
  have hnonneg : 0 ≤ (Matrix.trace (B⁻¹ * (B - A))).re :=
    (Complex.nonneg_iff.mp (V05Aux.trace_mul_nonneg hB.inv.posSemidef hle)).1
  have htrace : (Matrix.trace (B⁻¹ * A)).re ≤ n := by
    rw [Matrix.mul_sub, Matrix.trace_sub,
      Matrix.nonsing_inv_mul _ (hB.isUnit.map Matrix.detMonoidHom)] at hnonneg
    have ht : (Matrix.trace (1 : Herm n)).re = (n : ℝ) := by simp
    rw [Complex.sub_re, ht] at hnonneg
    linarith
  have hs := E02Aux.trace_logdet_support A B⁻¹ hA hB.inv
  rw [logdet_inverse_posDef B hB] at hs
  linarith

theorem logdet_minorant_le_upper
    (v : ComplexVector n → EReal) (C B : Herm n) (hC : C.PosDef) (hB : B.PosDef)
    (hupper : ∀ η, v η ≤ (ellipsoidQuadratic C η : EReal))
    (hBv : ∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η) :
    Real.log B.det.re ≤ Real.log C.det.re :=
  logdet_mono_posDef B C hB hC (psd_minorant_le_upper v C hC.isHermitian hupper hB.posSemidef hBv)

end Yau.NodeProofs.E01Aux
