import Yau.Proofs.C05MatrixTensorContraction
import Yau.Proofs.C05RealRicciJets
import Yau.Proofs.C05ScalarTimeEvolution
import Yau.Proofs.G01RawAlgebra
import Yau.LeafProofs.L23RicciDerivative

/-! The scalar Kähler--Ricci evolution uses one-half the actual real
Ricci tensor norm squared for `G = 2 Re h`. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem ricciNormSq_eq_half_realRicciNormSq (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) :
    ricciNormSq k x = (1 / 2 : ℝ) * covTensorNormSq (realMetricFn k x (chartPt x x))
      (realRicciJet k x 0 (chartPt x x)) := by
  let G := realMetricFn k x (chartPt x x)
  let A := Matrix.of (realRicciCoeff k x (chartPt x x))
  have hR : A = (2 : ℝ) • rawReal (ricci k x) := by
    ext a b
    exact Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw k hk hK x a b
  have hAsym : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    exact (realRicciCoeff_symm k hk x (mem_extChartAt_target x) a b).symm
  have hT : realRicciJet k x 0 (chartPt x x) = matrixCovTensor A := by
    funext v
    rfl
  have hnorm : covTensorNormSq G (realRicciJet k x 0 (chartPt x x)) =
      (G⁻¹ * A * G⁻¹ * A).trace := by
    rw [hT]
    exact covTensorPair_matrix G A A
      (Yau.LeafProofs.L18Aux.realMetricFn_isSymm k x _) hAsym
  have hGinv : G⁻¹ = (1 / 2 : ℝ) • rawReal (gMat k x)⁻¹ :=
    realMetricFn_inverse_eq k x _ (mem_extChartAt_target x)
  have hprod : G⁻¹ * A * G⁻¹ * A =
      rawReal ((gMat k x)⁻¹ * ricci k x * (gMat k x)⁻¹ * ricci k x) := by
    rw [hGinv, hR]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
    simp only [← rawReal_mul]
  change ricciNormSq k x = (1 / 2 : ℝ) * covTensorNormSq G _
  rw [hnorm, hprod, rawReal_trace]
  unfold ricciNormSq traceWith
  simp only [Matrix.mul_assoc]
  ring

end Yau.Proofs.C05Aux
