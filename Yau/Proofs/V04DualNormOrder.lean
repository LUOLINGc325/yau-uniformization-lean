import Yau.Proofs.V03DualNorm
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! The actual inverse-transpose covector norm reverses metric order.
The matrix argument also applies to the empty index type. -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

theorem dualNormMat_antitone {n : ℕ} {H G : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (hG : G.PosDef) (hHG : (G - H).PosSemidef)
    (ξ : ComplexVector n) : dualNormMat G ξ ≤ dualNormMat H ξ := by
  have hi : Ring.inverse G ≤ Ring.inverse H :=
    CStarAlgebra.ringInverse_le_ringInverse (Matrix.le_iff.mpr hHG) hH.isStrictlyPositive
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse] at hi
  have hpos := ((Matrix.le_iff.mp hi).transpose).dotProduct_mulVec_nonneg (WithLp.ofLp ξ)
  have hre := (Complex.nonneg_iff.mp hpos).1
  simpa only [Matrix.transpose_sub, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    dualNormMat, sub_nonneg] using hre

theorem setup_dualNorm_initial_le {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (x : X.manifold.Carrier)
    (ξ : Covector n) {t : ℝ} (ht : 0 ≤ t) :
    dualNorm (d.h 0) x ξ ≤ dualNorm (d.h t) x ξ := by
  have h0 : d.h 0 = X.metric.form := hd.2.2.1.1.1.1
  rw [h0]
  exact dualNormMat_antitone (gMat_posDef (d.h t) x) (gMat_posDef X.metric.form x)
    (hd.2.2.1.1.2.2.2.2.1 t ht x) (covectorCoords x x ξ)

end Yau.Blueprint.V04Proof
