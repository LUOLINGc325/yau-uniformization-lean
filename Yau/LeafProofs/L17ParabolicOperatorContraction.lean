import Yau.LeafProofs.L17SchauderSpaceNorm
import Yau.LeafProofs.L17MetricJetMaps

open Set Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicOperatorAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ}

theorem operator_realVec_norm (a : RIdx n) : ‖realVec a‖ = 1 := by
  by_cases h : a.2 = 0 <;> simp [realVec,h,norm_smul]

/-- The actual finite real Hessian contraction, linear in both entries. -/
def hessianContractionCLM (n : ℕ) :
    Matrix (RIdx n) (RIdx n) ℝ →L[ℝ] D2 n →L[ℝ] ℝ :=
  ∑ a, ∑ b, (matrixEntryCLM a b).smulRight
    ((ContinuousLinearMap.apply ℝ ℝ (realVec b)).comp
      (ContinuousLinearMap.apply ℝ (D1 n) (realVec a)))

theorem hessianContractionCLM_apply (a : Matrix (RIdx n) (RIdx n) ℝ) (H : D2 n) :
    hessianContractionCLM n a H = ∑ i, ∑ j, a i j*H (realVec i) (realVec j) := by
  simp only [hessianContractionCLM,sum_apply,ContinuousLinearMap.smulRight_apply,
    matrixEntryCLM_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,smul_eq_mul]

theorem hessianContractionCLM_eq_actual (a : Matrix (RIdx n) (RIdx n) ℝ)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) :
    hessianContractionCLM n a (fderiv ℝ (fderiv ℝ f) z) = realHessianContraction a f z :=
  hessianContractionCLM_apply a _

def contractionBudget (n : ℕ) : ℝ := (2*(n : ℝ))^2

theorem contractionBudget_nonneg (n : ℕ) : 0 ≤ contractionBudget n := sq_nonneg _

theorem hessianContractionCLM_bound (a : Matrix (RIdx n) (RIdx n) ℝ) (H : D2 n) :
    ‖hessianContractionCLM n a H‖ ≤ contractionBudget n*‖a‖*‖H‖ := by
  rw [hessianContractionCLM_apply]
  calc
    _ ≤ ∑ i, ‖∑ j, a i j*H (realVec i) (realVec j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖a i j*H (realVec i) (realVec j)‖ := Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : RIdx n, ∑ _j : RIdx n, ‖a‖*‖H‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hA : ‖a i j‖ ≤ ‖a‖ := (norm_le_pi_norm (a i) j).trans (norm_le_pi_norm a i)
      have hH : ‖H (realVec i) (realVec j)‖ ≤ ‖H‖ := by
        simpa only [operator_realVec_norm,mul_one] using
          ((H (realVec i)).le_opNorm (realVec j)).trans
            (mul_le_mul_of_nonneg_right (H.le_opNorm (realVec i)) (norm_nonneg _))
      rw [norm_mul]
      exact mul_le_mul hA hH (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [RIdx,contractionBudget]; ring

theorem hessianContractionCLM_difference (a b : Matrix (RIdx n) (RIdx n) ℝ) (H K : D2 n) :
    hessianContractionCLM n a H-hessianContractionCLM n b K =
      hessianContractionCLM n a (H-K)+hessianContractionCLM n (a-b) K := by
  simp only [map_sub,_root_.sub_apply]
  ring

theorem hessianContractionCLM_weighted_difference (r : ℝ)
    (a b : Matrix (RIdx n) (RIdx n) ℝ) (H K : D2 n) :
    r*(hessianContractionCLM n a H-hessianContractionCLM n b K) =
      hessianContractionCLM n a (r • (H-K))+hessianContractionCLM n (r • (a-b)) K := by
  rw [hessianContractionCLM_difference]
  simp only [map_smul,_root_.smul_apply,smul_eq_mul,mul_add]

end Yau.LeafProofs.L17ParabolicOperatorAux
