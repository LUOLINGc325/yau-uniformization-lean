import Yau.Proofs.C05CovariantHessianBlocks
import Yau.Proofs.C05IntrinsicJetCoordinates
import Yau.Proofs.C05InverseEnergyNaturalityAlgebra

/-! The Hermitian part of the actual real Hessian is a metric contraction.
The complex structure acts isometrically for G = 2 Re h. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Matrix Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem matrixCovTensor_congruence (J B : Matrix (RIdx n) (RIdx n) ℝ) :
    matrixCovTensor (Jᵀ*B*J) = tensorFrameTransform J (matrixCovTensor B) := by
  funext v
  have ht : tensorFrameTransform J (matrixCovTensor B) v =
      ∑ a, ∑ b, B a b * J a (v 0) * J b (v 1) := by
    unfold tensorFrameTransform
    rw [← (finTwoArrowEquiv (RIdx n)).symm.sum_comp]
    simp only [Fintype.sum_prod_type,finTwoArrowEquiv,Equiv.coe_fn_symm_mk,
      matrixCovTensor,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,mul_assoc]
  rw [ht]
  change (Jᵀ*B*J) (v 0) (v 1) = _
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem metricTensorNorm_J_congruence (k : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (B : Matrix (RIdx n) (RIdx n) ℝ) :
    metricTensorNorm (realMetricFn k c z) (matrixCovTensor ((jMatrix n)ᵀ*B*jMatrix n)) =
      metricTensorNorm (realMetricFn k c z) (matrixCovTensor B) := by
  have hi : (-jMatrix n) * jMatrix n = 1 := by rw [neg_mul,jMatrix_sq,neg_neg]
  have hdet := Matrix.det_ne_zero_of_left_inverse hi
  have hInv := inverseMatrix_congruence (jMatrix n) (realMetricFn k c z) hdet
  rw [jMatrix_metric_orthogonal k c z] at hInv
  rw [matrixCovTensor_congruence]
  unfold metricTensorNorm
  rw [covTensorNormSq_frameTransform _ _ _ hInv]

theorem hessianMixed_real_projection (B : Matrix (RIdx n) (RIdx n) ℝ) :
    (2:ℝ) • rawReal (hessianMixed B) = (1/2:ℝ) • (B + (jMatrix n)ᵀ*B*jMatrix n) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rw [Matrix.smul_apply,smul_eq_mul,Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,
    jMatrix_conjugation_apply]
  fin_cases a <;> fin_cases b <;>
    norm_num [rawReal,hessianMixed,jIndex,jSign] <;> ring

theorem hessianMixed_real_norm_le (k : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (B : Matrix (RIdx n) (RIdx n) ℝ) :
    metricTensorNorm (realMetricFn k c z) (matrixCovTensor ((2:ℝ) • rawReal (hessianMixed B))) ≤
      metricTensorNorm (realMetricFn k c z) (matrixCovTensor B) := by
  let G := realMetricFn k c z
  have hG := realMetricFn_posDef k c z hz
  have hJ := metricTensorNorm_J_congruence k c z B
  have hh := sqrt_covTensorNormSq_add_le G hG (matrixCovTensor B)
    (matrixCovTensor ((jMatrix n)ᵀ*B*jMatrix n))
  change metricTensorNorm G (_ + _) ≤ metricTensorNorm G _ + metricTensorNorm G _ at hh
  rw [hJ] at hh
  rw [hessianMixed_real_projection]
  change Real.sqrt (covTensorNormSq G
    (fun v => (1/2:ℝ) * (matrixCovTensor B + matrixCovTensor ((jMatrix n)ᵀ*B*jMatrix n)) v)) ≤ _
  rw [sqrt_covTensorNormSq_const_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  change (1/2:ℝ) * metricTensorNorm G _ ≤ _
  linarith

theorem scalarJet_two_matrix (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) :
    scalarJet k f c 2 z = matrixCovTensor (Matrix.of (Yau.Proofs.C05GradientFlowAux.realHessInChart k f c z)) := by
  funext v
  have hv : v = ![v 0,v 1] := by funext j; fin_cases j <;> rfl
  rw [hv,scalarJet_two]
  rfl

theorem realLevi_norm_le_scalarHessian (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    metricTensorNorm (realMetricFn k x (chartPt x x))
      (matrixCovTensor ((2:ℝ) • rawReal (levi f x))) ≤ scalarJetNorm k f 2 x := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hfc : ContDiffAt ℝ 2 (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  change metricTensorNorm (realMetricFn k x (chartPt x x))
    (matrixCovTensor ((2:ℝ) • rawReal (leviC (inChart x f) (chartPt x x)))) ≤ _
  rw [← hessianMixed_realHessInChart k hk hK f x hz hfc]
  have hb := hessianMixed_real_norm_le k x hz (Matrix.of (Yau.Proofs.C05GradientFlowAux.realHessInChart k f x (chartPt x x)))
  rw [← scalarJet_two_matrix] at hb
  exact hb

end Yau.Proofs.C05Aux
