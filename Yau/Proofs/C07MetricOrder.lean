import Yau.Proofs.Y03MetricSmooth
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Loewner order and the inverse-transpose cotangent quadratic forms. -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem hermLE_iff_inverse_order {H G : Herm n} (hH : H.PosDef) (hG : G.PosDef) :
    HermLE H G ↔ HermLE G⁻¹ H⁻¹ := by
  let a := Matrix.nonsingInvUnit G (hG.isUnit.map Matrix.detMonoidHom)
  let b := Matrix.nonsingInvUnit H (hH.isUnit.map Matrix.detMonoidHom)
  exact (CStarAlgebra.inv_le_inv_iff (a := a) (b := b)
    hG.posSemidef.nonneg hH.posSemidef.nonneg).symm

theorem hermLE_iff_dualNormMat_le {H G : Herm n} (hH : H.PosDef) (hG : G.PosDef) :
    HermLE H G ↔ ∀ ξ : ComplexVector n, dualNormMat G ξ ≤ dualNormMat H ξ := by
  rw [hermLE_iff_inverse_order hH hG]
  constructor
  · intro horder ξ
    have hp := (Complex.nonneg_iff.mp
      (horder.transpose.dotProduct_mulVec_nonneg (WithLp.ofLp ξ))).1
    simpa only [dualNormMat, Matrix.transpose_sub, Matrix.sub_mulVec, dotProduct_sub,
      Complex.sub_re, sub_nonneg] using hp
  · intro hdual
    apply Matrix.posSemidef_transpose_iff.mp
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hH.inv.isHermitian.sub hG.inv.isHermitian).transpose)
    intro v
    rw [Matrix.transpose_sub, Matrix.sub_mulVec, dotProduct_sub]
    apply sub_nonneg.mpr
    apply Complex.le_def.mpr
    refine ⟨hdual (WithLp.toLp 2 v), ?_⟩
    have hHim := (Complex.nonneg_iff.mp
      (hH.inv.transpose.posSemidef.dotProduct_mulVec_nonneg v)).2
    have hGim := (Complex.nonneg_iff.mp
      (hG.inv.transpose.posSemidef.dotProduct_mulVec_nonneg v)).2
    exact hGim.symm.trans hHim

end Yau.Proofs.C07Aux
