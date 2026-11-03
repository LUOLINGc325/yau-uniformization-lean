import Yau.Proofs.E01FeasibleCompact
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! The genuine inverse-transpose quadratic norm reverses the metric order. -/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem inverse_transpose_antitone (H G : Herm n) (hH : H.PosDef) (hG : G.PosDef)
    (hle : (G - H).PosSemidef) : ((H⁻¹)ᵀ - (G⁻¹)ᵀ).PosSemidef := by
  have horder : H ≤ G := sub_nonneg.mp hle.nonneg
  have hinv : Ring.inverse G ≤ Ring.inverse H :=
    CStarAlgebra.antitoneOn_ringInverse hH.isStrictlyPositive hG.isStrictlyPositive horder
  have hinv' : G⁻¹ ≤ H⁻¹ := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using hinv
  have hdiff : (H⁻¹ - G⁻¹).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hinv')
  simpa only [Matrix.transpose_sub] using hdiff.transpose

theorem dualNormMat_antitone (H G : Herm n) (hH : H.PosDef) (hG : G.PosDef)
    (hle : (G - H).PosSemidef) (ξ : ComplexVector n) :
    dualNormMat G ξ ≤ dualNormMat H ξ := by
  have hq := ellipsoidQuadratic_nonneg (inverse_transpose_antitone H G hH hG hle) ξ
  rw [ellipsoidQuadratic_sub] at hq
  exact sub_nonneg.mp hq

end Yau.NodeProofs.E01Aux
