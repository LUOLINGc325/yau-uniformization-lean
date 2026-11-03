import Yau.LeafProofs.L12

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ}

theorem realCoord_I_smul (v : ComplexVector n) (a : RIdx n) :
    realCoord (Complex.I • v) a = jSign (jIndex n a) * realCoord v (jIndex n a) := by
  rcases a with ⟨i, a⟩
  fin_cases a <;> simp [realCoord, jIndex, jSign, smul_eq_mul, Complex.mul_re, Complex.mul_im]

theorem I_smul_realVec (a : RIdx n) :
    Complex.I • realVec a = jSign a • realVec (jIndex n a) := by
  rcases a with ⟨i, a⟩
  fin_cases a <;> simp [realVec, jIndex, jSign, smul_smul, Complex.I_mul_I]

end Yau.Blueprint.C02Proof
