import Yau.Proofs.C03LogDualBasic
import Yau.Proofs.C03LogDualScalar

/-! The genuine inverse order bound and the exact uniform logarithmic estimate. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open Set Filter
namespace Yau.Proofs.C03Aux.LogDual
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem dualNormMat_real_one (d : ℝ) (hd : 0 < d) (xi : ComplexVector n) :
    dualNormMat ((d : ℂ) • (1 : Herm n)) xi = ‖xi‖ ^ 2 / d := by
  change ellipsoidQuadratic ((((d : ℂ) • (1 : Herm n))⁻¹)ᵀ) xi = _
  rw [real_scalar_identity_inverse_transpose d hd,
    ellipsoidQuadratic_real_smul, ellipsoidQuadratic_one]
  ring

theorem dualSquared_le_of_lower (H : ComplexVector n → Herm n)
    (z xi : ComplexVector n) (hPos : (H z).PosDef) (d : ℝ) (hd : 0 < d)
    (hLo : HermLE ((d : ℂ) • (1 : Herm n)) (H z)) :
    dualSquared H xi z ≤ ‖xi‖ ^ 2 / d := by
  have hsmall : (((d : ℂ) • (1 : Herm n)) : Herm n).PosDef :=
    (Matrix.PosDef.one : (1 : Herm n).PosDef).smul (Complex.zero_lt_real.mpr hd)
  exact (dualNormMat_antitone ((d : ℂ) • (1 : Herm n)) (H z)
    hsmall hPos hLo xi).trans_eq (dualNormMat_real_one d hd xi)

theorem logDual_le_of_lower (H : ComplexVector n → Herm n)
    (z xi : ComplexVector n) (hxi : xi ≠ 0) (hPos : (H z).PosDef) (d : ℝ) (hd : 0 < d)
    (hLo : HermLE ((d : ℂ) • (1 : Herm n)) (H z)) :
    logDual H xi z ≤ max 0 (-Real.log d) + 2 * Real.log (1 + ‖xi‖) := by
  exact log_le_uniform_bound (dualSquared H xi z) ‖xi‖ d
    (dualSquared_pos hPos hxi) (norm_pos_iff.mpr hxi) hd
    (dualSquared_le_of_lower H z xi hPos d hd hLo)

theorem logDual_eq_zero_of_normalized (H : ComplexVector n → Herm n)
    (xi o : ComplexVector n) (hqo : dualNormMat (H o) xi = 1) :
    logDual H xi o = 0 := by
  simp only [logDual, dualSquared, hqo, Real.log_one]

end Yau.Proofs.C03Aux.LogDual

