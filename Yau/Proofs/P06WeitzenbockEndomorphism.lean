import Yau.Proofs.P06WeitzenbockCurvature

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- Relative real endomorphism attached to a two-form in the actual chart. -/
def relativeEndomorphism (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) : Matrix (RIdx n) (RIdx n) ℝ :=
  (realMetricFn h c z)⁻¹ * chartFormMatrix A c z * jMatrix n

def covariantTwoMatrix (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) (a : RIdx n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun b d => covariantTwo h A c z a b d

theorem chartFormMatrix_derivative (h : HermitianField M) (A : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) (a : RIdx n) :
    matrixDirectionalDerivative (chartFormMatrix A c) z (realVec a) =
      covariantTwoMatrix h A c z a +
        (connectionMatrix h c z a)ᵀ * chartFormMatrix A c z +
        chartFormMatrix A c z * connectionMatrix h c z a := by
  ext b d
  simp only [matrixDirectionalDerivative, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, connectionMatrix, covariantTwoMatrix,
    covariantTwo_formula, rDeriv]
  simp only [mul_comm]
  ring

/-- The actual connection on endomorphisms is a derivation. This identity
does not need closedness, or even the (1,1) type of the input two-form. -/
theorem relativeEndomorphism_covariant_derivative (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h) (A : RealForm M 2)
    (hA : SmoothRealForm A) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (a : RIdx n) :
    matrixDirectionalDerivative (relativeEndomorphism h A c) z (realVec a) +
        connectionMatrix h c z a * relativeEndomorphism h A c z -
        relativeEndomorphism h A c z * connectionMatrix h c z a =
      (realMetricFn h c z)⁻¹ * covariantTwoMatrix h A c z a * jMatrix n := by
  have hH (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => (realMetricFn h c w)⁻¹ i j) z :=
    ((realMetricFn_inverse_contDiffOn h hs c i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hK (i j : RIdx n) : DifferentiableAt ℝ (fun w => chartFormMatrix A c w i j) z :=
    ((hA c ![i,j]).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hJ (i j : RIdx n) : DifferentiableAt ℝ (fun _ : ComplexVector n => jMatrix n i j) z :=
    differentiableAt_const _
  have hHK := matrix_entries_differentiable_mul hH hK
  have hzero : matrixDirectionalDerivative (fun _ : ComplexVector n => jMatrix n) z
      (realVec a) = 0 := by
    ext i j
    simp [matrixDirectionalDerivative]
  unfold relativeEndomorphism
  rw [matrixDirectionalDerivative_mul hHK hJ,
    matrixDirectionalDerivative_mul hH hK, hzero, Matrix.mul_zero, add_zero,
    inverseMetric_directional_derivative h hs c hz a, chartFormMatrix_derivative]
  have hcomm := (G01Aux.connectionMatrix_commute_jMatrix h hs hk c z hz a).eq
  have hcomm' : jMatrix n * connectionMatrix h c z a =
      connectionMatrix h c z a * jMatrix n := hcomm.symm
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_assoc]
  rw [hcomm']
  abel

theorem relativeEndomorphism_center_eq_raw (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (x : M.Carrier) :
    relativeEndomorphism h A x (chartPt x x) =
      G01Aux.rawReal ((gMat h x)⁻¹ * formHermitianMatrix A x) := by
  have hK : chartFormMatrix A x (chartPt x x) = realFormMatrix A x := by
    ext a b
    exact formComponents_center_pair A x ![a,b]
  rw [relativeEndomorphism, hK,
    G01Aux.realMetricFn_inverse_eq h x (chartPt x x) (mem_extChartAt_target x),
    realFormMatrix_eq_raw A h11 x]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) = -1 by norm_num, neg_one_smul]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, jMatrix_sq]
  simp only [Matrix.mul_neg, Matrix.mul_one, neg_neg]
  rw [← G01Aux.rawReal_mul]
  rfl

end Yau.NodeProofs.P06Weitzenbock
