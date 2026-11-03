import Yau.Proofs.C03LogDualCauchy
import Yau.Proofs.E01ProductDualLevi
import Yau.Proofs.E01DualOrder

/-! Genuine smoothness and positive quadratic data for a constant cotangent vector. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open Set Filter
namespace Yau.Proofs.C03Aux.LogDual
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

def dualSquared (H : ComplexVector n → Herm n) (xi z : ComplexVector n) : ℝ :=
  dualNormMat (H z) xi

def logDual (H : ComplexVector n → Herm n) (xi z : ComplexVector n) : ℝ :=
  Real.log (dualSquared H xi z)

def connectionVector (H : ComplexVector n → Herm n) (z xi a : ComplexVector n) :
    ComplexVector n :=
  -matrixFiberMap ((complexMatrixWirt H z a)ᵀ * ((H z)⁻¹)ᵀ) xi

def computedResidual (H : ComplexVector n → Herm n) (z xi a : ComplexVector n) : ℝ :=
  ellipsoidQuadratic
    (((H z)⁻¹)ᵀ * ((complexMatrixWirt H z a)ᵀ * ((H z)⁻¹)ᵀ *
      ((complexMatrixWirt H z a)ᴴ)ᵀ -
      (complexMatrixWirt (fun w => complexMatrixWirtBar H w a) z a)ᵀ) *
      ((H z)⁻¹)ᵀ) xi

def matrixPairing (K : Herm n) (xi c : ComplexVector n) : ℂ :=
  star (WithLp.ofLp xi) ⬝ᵥ (K *ᵥ WithLp.ofLp c)

theorem dualSquared_pos {H : ComplexVector n → Herm n} {xi z : ComplexVector n}
    (hH : (H z).PosDef) (hxi : xi ≠ 0) : 0 < dualSquared H xi z :=
  ellipsoidQuadratic_pos hH.inv.transpose hxi

theorem dualSquared_contDiffOn {U : Set (ComplexVector n)}
    (H : ComplexVector n → Herm n)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef) (xi : ComplexVector n) :
    ContDiffOn ℝ ∞ (dualSquared H xi) U := by
  have hinv (i j : Fin n) : ContDiffOn ℝ ∞ (fun z => (H z)⁻¹ i j) U :=
    entrywise_matrix_inv_contDiffOn hH (fun z hz => (hPos z hz).det_pos.ne') i j
  have hC : ContDiffOn ℝ ∞ (fun z => ∑ i, star (xi i) * ∑ j, (H z)⁻¹ j i * xi j) U :=
    ContDiffOn.sum fun i _ => contDiffOn_const.mul
      (ContDiffOn.sum fun j _ => (hinv j i).mul contDiffOn_const)
  exact Complex.reCLM.contDiff.comp_contDiffOn hC

theorem logDual_contDiffOn {U : Set (ComplexVector n)}
    (H : ComplexVector n → Herm n)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef) (xi : ComplexVector n) (hxi : xi ≠ 0) :
    ContDiffOn ℝ ∞ (logDual H xi) U :=
  (dualSquared_contDiffOn H hH hPos xi).log
    (fun z hz => (dualSquared_pos (hPos z hz) hxi).ne')

theorem dualNormMat_product_contDiffOn {U : Set (ComplexVector n)}
    (H : ComplexVector n → Herm n)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n => dualNormMat (H p.1) p.2) (U ×ˢ univ) := by
  have hx (i : Fin n) : ContDiffOn ℝ ∞ (fun p : CotangentCoord n => p.2 i) (U ×ˢ univ) :=
    ((contDiff_piLp_apply (p := 2) (i := i)).comp contDiff_snd).contDiffOn
  have hinv (i j : Fin n) : ContDiffOn ℝ ∞
      (fun p : CotangentCoord n => (H p.1)⁻¹ i j) (U ×ˢ univ) :=
    (entrywise_matrix_inv_contDiffOn hH (fun z hz => (hPos z hz).det_pos.ne') i j).comp
      contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hC : ContDiffOn ℝ ∞ (fun p : CotangentCoord n =>
      ∑ i, star (p.2 i) * ∑ j, (H p.1)⁻¹ j i * p.2 j) (U ×ˢ univ) :=
    ContDiffOn.sum fun i _ => (Complex.conjCLE.contDiff.comp_contDiffOn (hx i)).mul
      (ContDiffOn.sum fun j _ => (hinv j i).mul (hx j))
  exact Complex.reCLM.contDiff.comp_contDiffOn hC

theorem matrixPairing_cauchy (K : Herm n) (hK : K.PosDef) (xi c : ComplexVector n) :
    ‖matrixPairing K xi c‖ ^ 2 ≤ ellipsoidQuadratic K xi * ellipsoidQuadratic K c := by
  exact positive_matrix_cauchy K hK (WithLp.ofLp xi) (WithLp.ofLp c)

end Yau.Proofs.C03Aux.LogDual

