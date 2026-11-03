import Yau.Proofs.E01Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The original inverse-transpose cometric has exactly the negative metric log determinant. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem logdet_inverse_posDef (A : Herm n) (hA : A.PosDef) :
    Real.log (A⁻¹).det.re = -Real.log A.det.re := by
  have hAi : A.det.im = 0 := (Complex.pos_iff.mp hA.det_pos).2.symm
  have hAr : A.det = (A.det.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hAi
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hAr]
  rw [← Complex.ofReal_inv, Complex.ofReal_re, Real.log_inv]
  rfl

theorem cometric_logdet_eq_neg_logdet (A : Herm n) (hA : A.PosDef) :
    Real.log ((A⁻¹)ᵀ).det.re = -Real.log A.det.re := by
  rw [Matrix.det_transpose]
  exact logdet_inverse_posDef A hA

theorem cometric_posDef (A : Herm n) (hA : A.PosDef) : ((A⁻¹)ᵀ).PosDef := hA.inv.transpose

end Yau.NodeProofs.E01Aux
