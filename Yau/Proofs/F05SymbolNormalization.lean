import Yau.Proofs.F05AtlasModel
import Yau.Proofs.F04ChartCoefficients
import Yau.LeafProofs.L17ScalarChartOperator
import Yau.LeafProofs.L16ChartOperatorAlgebra

/-! Exact polarization normalization of the original complex Laplacian. -/

open Set
open scoped Topology ContDiff Manifold Matrix
noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_realCoord_contDiff (i : RIdx n) :
    ContDiff ℝ ∞ (fun z : Space n => realCoord z i) := by
  simpa only [← realCoordLinear_apply] using (realCoordLinear i).contDiff

theorem F05_realCoord_fderiv (i : RIdx n) (z : Space n) :
    fderiv ℝ (fun w : Space n => realCoord w i) z = realCoordLinear i := by
  simpa only [← realCoordLinear_apply] using (realCoordLinear i).fderiv

theorem F05_realCoord_secondFDeriv (i : RIdx n) (z : Space n) :
    fderiv ℝ (fderiv ℝ (fun w : Space n => realCoord w i)) z = 0 := by
  have heq : fderiv ℝ (fun w : Space n => realCoord w i) = fun _ => realCoordLinear i :=
    funext (F05_realCoord_fderiv i)
  rw [heq,fderiv_const_apply]

theorem F05_coordinate_product_hessian (i j : RIdx n) (z v w : Space n) :
    fderiv ℝ (fderiv ℝ (fun y : Space n => realCoord y i * realCoord y j)) z v w =
      realCoord v i * realCoord w j + realCoord w i * realCoord v j := by
  rw [secondFDeriv_mul_apply ((F05_realCoord_contDiff i).contDiffAt.of_le (by simp))
    ((F05_realCoord_contDiff j).contDiffAt.of_le (by simp))]
  simp only [F05_realCoord_fderiv,F05_realCoord_secondFDeriv,
    ContinuousLinearMap.zero_apply,realCoordLinear_apply,mul_zero,zero_add,add_zero]

theorem F05_coordinate_product_contraction (B : Mat n) (i j : RIdx n) (z : Space n) :
    (∑ a, ∑ b, B a b *
      fderiv ℝ (fderiv ℝ (fun y : Space n => realCoord y i * realCoord y j)) z
        (realVec a) (realVec b)) = B i j + B j i := by
  classical
  simp only [F05_coordinate_product_hessian,Yau.LeafProofs.L12Aux.realCoord_realVec,
    mul_add,Finset.sum_add_distrib]
  simp [eq_comm]

theorem F05_baseA_eq_real_inverse (h : HermitianField M) (x : M.Carrier)
    {z : Space n} (hz : z ∈ chartTarget x) :
    baseA h x z = fun i j => (1/2 : ℝ) * (realMetricFn h x z)⁻¹ i j := by
  funext i j
  have hq : ContDiffAt ℝ ∞ (fun y : Space n => realCoord y i * realCoord y j) z :=
    ((F05_realCoord_contDiff i).mul (F05_realCoord_contDiff j)).contDiffAt
  have hp := principal_realLaplacian_eq_twice_traceWith h x hz (hq.of_le (by simp))
  rw [F05_coordinate_product_contraction] at hp
  have hs := (realMetricFn_isSymm h x z).inv.apply i j
  dsimp only [baseA]
  linarith

theorem F05_baseA_eq_flowChartPrincipal (h : ℝ → HermitianField M) (x : M.Carrier)
    {z : Space n} (hz : z ∈ chartTarget x) (t : ℝ) :
    baseA (h t) x z = Yau.F04Proof.flowChartPrincipal h x (z,t) :=
  F05_baseA_eq_real_inverse (h t) x hz

theorem F05_baseA_eq_scalarSymbol (h : HermitianField M) (x : M.Carrier)
    {z : Space n} (hz : z ∈ chartTarget x) :
    baseA h x z = Yau.LeafProofs.L17Aux.scalarSymbol (hMat h x z) := by
  rw [F05_baseA_eq_real_inverse h x hz,realMetricFn_inverse h x hz]
  ext i j
  simp only [Yau.LeafProofs.L17Aux.scalarSymbol,
    Yau.LeafProofs.L17Aux.scalarRealification,Matrix.smul_apply,smul_eq_mul,
    realRepresentation_apply]
  ring

theorem F05_baseA_isSymm (h : HermitianField M) (x : M.Carrier)
    {z : Space n} (hz : z ∈ chartTarget x) : (baseA h x z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have he := F05_baseA_eq_real_inverse h x hz
  change baseA h x z j i = baseA h x z i j
  rw [congrFun (congrFun he j) i,congrFun (congrFun he i) j]
  rw [(realMetricFn_isSymm h x z).inv.apply i j]

end Yau.Proofs.F05Aux
