import Yau.Proofs.C05RicciTimePolynomialBudgetAlgebra
import Yau.Proofs.C05ThirdScalarTimeDefinitions
import Yau.Proofs.C05MetricTracePowers

/-! Intrinsic bounds for the original three complex trace polynomials. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciTimePolynomialBudgetAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05ThirdScalarTimeAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem realRicci_endomorphism_center (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) :
    (realMetricFn k x (chartPt x x))⁻¹ * Matrix.of (realRicciCoeff k x (chartPt x x)) =
      rawReal ((gMat k x)⁻¹ * ricci k x) := by
  have hR : Matrix.of (realRicciCoeff k x (chartPt x x)) = (2:ℝ) • rawReal (ricci k x) := by
    ext a b
    exact Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw k hk hK x a b
  have hGinv : (realMetricFn k x (chartPt x x))⁻¹ = (1/2:ℝ) • rawReal (gMat k x)⁻¹ :=
    realMetricFn_inverse_eq k x _ (mem_extChartAt_target x)
  rw [hGinv,hR]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  norm_num
  exact (rawReal_mul _ _).symm

theorem realLevi_endomorphism_center (k : HermitianField M) (x : M.Carrier)
    (H : Matrix (Fin n) (Fin n) ℂ) :
    (realMetricFn k x (chartPt x x))⁻¹ * ((2:ℝ) • rawReal H) =
      rawReal ((gMat k x)⁻¹ * H) := by
  have hGinv : (realMetricFn k x (chartPt x x))⁻¹ = (1/2:ℝ) • rawReal (gMat k x)⁻¹ :=
    realMetricFn_inverse_eq k x _ (mem_extChartAt_target x)
  rw [hGinv]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  norm_num
  exact (rawReal_mul _ _).symm

theorem ricciSquareLevi_real_trace (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) :
    let G := realMetricFn k x (chartPt x x)
    let A := Matrix.of (realRicciCoeff k x (chartPt x x))
    let H := (2:ℝ) • rawReal (levi (scalarCurvature k) x)
    (G⁻¹*A*G⁻¹*A*G⁻¹*H).trace = 2 * ricciSquareLevi k x := by
  dsimp only
  have he : (realMetricFn k x (chartPt x x))⁻¹ * Matrix.of (realRicciCoeff k x (chartPt x x)) *
      (realMetricFn k x (chartPt x x))⁻¹ * Matrix.of (realRicciCoeff k x (chartPt x x)) *
      (realMetricFn k x (chartPt x x))⁻¹ * ((2:ℝ) • rawReal (levi (scalarCurvature k) x)) =
      rawReal (((gMat k x)⁻¹ * ricci k x) * ((gMat k x)⁻¹ * ricci k x) *
        ((gMat k x)⁻¹ * levi (scalarCurvature k) x)) := by
    conv_lhs => rw [show ∀ (G A H : Matrix (RIdx n) (RIdx n) ℝ),
      G*A*G*A*G*H = (G*A)*(G*A)*(G*H) by intros; simp only [Matrix.mul_assoc]]
    rw [realRicci_endomorphism_center k hk hK,realLevi_endomorphism_center]
    simp only [rawReal_mul]
  rw [he,rawReal_trace]
  rfl

theorem leviScalarSquare_real_trace (k : HermitianField M) (x : M.Carrier) :
    let G := realMetricFn k x (chartPt x x)
    let H := (2:ℝ) • rawReal (levi (scalarCurvature k) x)
    (G⁻¹*H*G⁻¹*H).trace = 2 * leviScalarSquare k x := by
  dsimp only
  have he : (realMetricFn k x (chartPt x x))⁻¹ * ((2:ℝ) • rawReal (levi (scalarCurvature k) x)) *
      (realMetricFn k x (chartPt x x))⁻¹ * ((2:ℝ) • rawReal (levi (scalarCurvature k) x)) =
      rawReal (((gMat k x)⁻¹ * levi (scalarCurvature k) x) *
        ((gMat k x)⁻¹ * levi (scalarCurvature k) x)) := by
    conv_lhs => rw [show ∀ (G H : Matrix (RIdx n) (RIdx n) ℝ),
      G*H*G*H = (G*H)*(G*H) by intros; simp only [Matrix.mul_assoc]]
    rw [realLevi_endomorphism_center]
    simp only [rawReal_mul]
  rw [he,rawReal_trace]
  rfl

theorem ricciQuartic_real_trace (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) :
    let G := realMetricFn k x (chartPt x x)
    let A := Matrix.of (realRicciCoeff k x (chartPt x x))
    (G⁻¹*A*G⁻¹*A*G⁻¹*A*G⁻¹*A).trace = 2 * ricciQuartic k x := by
  have hh := realRicciTracePower_center k hk hK 4 x
  simpa only [realRicciTracePower,ricciQuartic,pow_succ,pow_zero,Matrix.one_mul,
    Matrix.mul_assoc] using hh

theorem dimension_budget :
    1 ≤ ((2*n:ℕ)+1:ℝ) ^ 2 ∧
      (2*n:ℕ) ≤ ((2*n:ℕ)+1:ℝ) ^ 2 ∧
      Real.sqrt (2*n:ℕ) ≤ ((2*n:ℕ)+1:ℝ) ^ 2 := by
  have hd : (0:ℝ) ≤ (2*n:ℕ) := Nat.cast_nonneg _
  have hs := Real.sq_sqrt hd
  have hsn := Real.sqrt_nonneg (2*n:ℕ)
  constructor
  · nlinarith [sq_nonneg ((2*n:ℕ):ℝ)]
  constructor
  · nlinarith [sq_nonneg ((2*n:ℕ):ℝ)]
  · have hh : Real.sqrt (2*n:ℕ) ≤ (2*n:ℕ)+1 := by nlinarith
    nlinarith [sq_nonneg ((2*n:ℕ):ℝ)]

theorem ricciSquareLevi_abs_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) :
    let G := realMetricFn k x (chartPt x x)
    let NA := metricTensorNorm G (matrixCovTensor (Matrix.of (realRicciCoeff k x (chartPt x x))))
    let NH := metricTensorNorm G (matrixCovTensor ((2:ℝ) • rawReal (levi (scalarCurvature k) x)))
    |ricciSquareLevi k x| ≤ ((2*n:ℕ)+1:ℝ) ^ 2 * NA ^ 2 * NH := by
  dsimp only
  let G := realMetricFn k x (chartPt x x)
  let A := Matrix.of (realRicciCoeff k x (chartPt x x))
  let H := (2:ℝ) • rawReal (levi (scalarCurvature k) x)
  have hh := trace_cubic_abs_le G A H (realMetricFn_posDef k x _ (mem_extChartAt_target x))
  rw [ricciSquareLevi_real_trace k hk hK,abs_mul] at hh
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have hn := metricTensorNorm_nonneg G (matrixCovTensor H)
  have hb := mul_le_mul_of_nonneg_right (dimension_budget (n:=n)).2.2
    (mul_nonneg (sq_nonneg (metricTensorNorm G (matrixCovTensor A))) hn)
  change |ricciSquareLevi k x| ≤ _
  nlinarith [abs_nonneg (ricciSquareLevi k x)]

theorem leviScalarSquare_abs_le (k : HermitianField M) (x : M.Carrier) :
    let G := realMetricFn k x (chartPt x x)
    let NH := metricTensorNorm G (matrixCovTensor ((2:ℝ) • rawReal (levi (scalarCurvature k) x)))
    |leviScalarSquare k x| ≤ ((2*n:ℕ)+1:ℝ) ^ 2 * NH ^ 2 := by
  dsimp only
  let G := realMetricFn k x (chartPt x x)
  let H := (2:ℝ) • rawReal (levi (scalarCurvature k) x)
  have hh := trace_square_abs_le G H (realMetricFn_posDef k x _ (mem_extChartAt_target x))
  rw [leviScalarSquare_real_trace k x,abs_mul] at hh
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have hb := mul_le_mul_of_nonneg_right (dimension_budget (n:=n)).1
    (sq_nonneg (metricTensorNorm G (matrixCovTensor H)))
  nlinarith [abs_nonneg (leviScalarSquare k x)]

theorem ricciQuartic_abs_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) :
    let G := realMetricFn k x (chartPt x x)
    let NA := metricTensorNorm G (matrixCovTensor (Matrix.of (realRicciCoeff k x (chartPt x x))))
    |ricciQuartic k x| ≤ ((2*n:ℕ)+1:ℝ) ^ 2 * NA ^ 4 := by
  dsimp only
  let G := realMetricFn k x (chartPt x x)
  let A := Matrix.of (realRicciCoeff k x (chartPt x x))
  have hh := trace_quartic_abs_le G A (realMetricFn_posDef k x _ (mem_extChartAt_target x))
  rw [ricciQuartic_real_trace k hk hK,abs_mul] at hh
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have hb := mul_le_mul_of_nonneg_right (dimension_budget (n:=n)).2.1
    (show 0 ≤ metricTensorNorm G (matrixCovTensor A) ^ 4 by positivity)
  nlinarith [abs_nonneg (ricciQuartic k x)]

end Yau.Proofs.C05RicciTimePolynomialBudgetAux
