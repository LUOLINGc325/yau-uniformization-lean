import Yau.Proofs.G01ChernRealCurvature
import Yau.Proofs.G01RawDerivative
import Yau.Proofs.G01RawPairing
import Yau.Proofs.G01RmAlgebra

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem chernRealA_differentiableAt (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (a : RIdx n) (i j : Fin n) :
    DifferentiableAt ℝ (fun w => chernRealA h x w a i j) z := by
  have hA := ((chernA_contDiffOn h hs x a.1 i j).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  by_cases ha : a.2 = 0
  · simpa only [chernRealA, ha, ite_true] using hA
  · simpa only [chernRealA, ha, ite_false, Matrix.smul_apply, smul_eq_mul] using
      hA.const_mul Complex.I

/-- The actual Levi-Civita curvature matrix is the unprojected real representation of the Chern calculation. -/
theorem curvatureMatrix_eq_rawReal (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    L12Aux.curvatureMatrix h x z a b =
      rawReal (complexCurvatureRealDirections h x z a b) := by
  have hD (p q : RIdx n) : L12Aux.connectionDerivativeMatrix h x z p q =
      rawReal (matrixRealDerivative (fun w => chernRealA h x w q) z p) := by
    change L12Aux.matrixDirectionalDerivative (fun w => L12Aux.connectionMatrix h x w q)
      z (realVec p) = _
    have he : (fun w => L12Aux.connectionMatrix h x w q) =ᶠ[𝓝 z]
        (fun w => rawReal (chernRealA h x w q)) := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
      exact connectionMatrix_eq_chernRealA h hs hk x w hw q
    rw [L12Aux.matrixDirectionalDerivative_congr he]
    exact rawReal_derivative _ z (chernRealA_differentiableAt h hs x z hz q) p
  rw [L12Aux.curvatureMatrix_eq, hD a b, hD b a,
    connectionMatrix_eq_chernRealA h hs hk x z hz a,
    connectionMatrix_eq_chernRealA h hs hk x z hz b]
  simp only [complexCurvatureRealDirections, rawReal_sub, rawReal_add, rawReal_mul]

/-- Lowering this comparison uses the same real metric G = 2 Re h. -/
theorem curvature4_eq_rawReal (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    L12Aux.curvature4 h x z a b c d =
      2 * rawReal (hMat h x z * complexCurvatureRealDirections h x z a b) d c := by
  have hR := curvatureMatrix_eq_rawReal h hs hk x z hz a b
  rw [rawReal_mul]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  unfold L12Aux.curvature4
  apply Finset.sum_congr rfl
  intro l _
  have hl := congrArg (fun A => A l c) hR
  change riemannCoeff h x z a b c l = rawReal (complexCurvatureRealDirections h x z a b) l c at hl
  rw [← hl]
  have hG := L12Aux.realMetricFn_entries h x z d l
  change realMetricFn h x z d l = 2 * rawReal (hMat h x z) d l at hG
  rw [← mul_assoc, ← hG, L12Aux.realMetricFn_symm h x z d l]

end Yau.NodeProofs.G01Aux
