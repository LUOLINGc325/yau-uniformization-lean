import Yau.LeafProofs.L17NormalizedPotential
import Yau.LeafProofs.L17BanachLogarithm

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux L17LocalHolderBanachAlgebraAux
open L17BanachLogarithmAux
local instance matrixLogHolderTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

def matrixRealTraceLinearMap (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ)

def matrixRealTraceCLM (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
  { matrixRealTraceLinearMap n with cont := (matrixRealTraceLinearMap n).continuous_of_finiteDimensional }

theorem matrixRealTraceCLM_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    matrixRealTraceCLM n H=(Matrix.trace H).re := rfl

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ)

def matrixRealTraceBanachCLM :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ →L[ℝ] LocalHolderBanach ℝ P T γ :=
  (valueContinuousLinearEquiv ℝ P T γ).symm.toContinuousLinearMap.comp
    ((localMapCLM (matrixRealTraceCLM n)).comp
      (valueContinuousLinearEquiv (Matrix (Fin n) (Fin n) ℂ) P T γ).toContinuousLinearMap)

theorem matrixRealTraceBanachCLM_value
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) (q : LocalCylinder P T) :
    matrixRealTraceBanachCLM P T γ u q=(Matrix.trace (u q)).re := rfl

theorem matrixRealTraceBanachCLM_norm_le
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) :
    ‖matrixRealTraceBanachCLM P T γ u‖ ≤ ‖matrixRealTraceCLM n‖*‖u‖ := by
  rw [norm_eq_twice,norm_eq_twice]
  exact (mul_le_mul_of_nonneg_left (localMapElement_norm_le (matrixRealTraceCLM n) u.value)
    (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

def matrixHolderEvalContinuousAlgHom (q : LocalCylinder P T) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ →A[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  { evalAlgHom (Matrix (Fin n) (Fin n) ℂ) P T γ q with
    cont := (evalCLM (Matrix (Fin n) (Fin n) ℂ) P T γ q).continuous }

theorem matrix_logIncrement_value
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) (hu : ‖u‖<1)
    (q : LocalCylinder P T) :
    logIncrement (LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) u q =
      logIncrement (Matrix (Fin n) (Fin n) ℂ) (u q) :=
  logIncrement_map (matrixHolderEvalContinuousAlgHom P T γ q) hu

theorem matrix_logRemainder_value
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) (hu : ‖u‖<1)
    (q : LocalCylinder P T) :
    logRemainder (LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) u q =
      logRemainder (Matrix (Fin n) (Fin n) ℂ) (u q) :=
  logRemainder_map (matrixHolderEvalContinuousAlgHom P T γ q) hu

theorem matrixRealTraceBanachCLM_opNorm_le :
    ‖matrixRealTraceBanachCLM P T γ‖ ≤ ‖matrixRealTraceCLM n‖ :=
  (matrixRealTraceBanachCLM P T γ).opNorm_le_bound (norm_nonneg _)
    (matrixRealTraceBanachCLM_norm_le P T γ)

def matrixTraceLogIncrement
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) : LocalHolderBanach ℝ P T γ :=
  matrixRealTraceBanachCLM P T γ (logIncrement _ u)

def matrixTraceLogRemainder
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) : LocalHolderBanach ℝ P T γ :=
  matrixRealTraceBanachCLM P T γ (logRemainder _ u)

theorem matrixTraceLogIncrement_value
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) (hu : ‖u‖<1)
    (q : LocalCylinder P T) :
    matrixTraceLogIncrement P T γ u q=(Matrix.trace (logIncrement _ (u q))).re := by
  rw [matrixTraceLogIncrement,matrixRealTraceBanachCLM_value,matrix_logIncrement_value P T γ u hu]

theorem matrixTraceLogRemainder_value
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) (hu : ‖u‖<1)
    (q : LocalCylinder P T) :
    matrixTraceLogRemainder P T γ u q=(Matrix.trace (logRemainder _ (u q))).re := by
  rw [matrixTraceLogRemainder,matrixRealTraceBanachCLM_value,matrix_logRemainder_value P T γ u hu]

theorem matrixTraceLogIncrement_contDiffOn :
    ContDiffOn ℝ ∞ (matrixTraceLogIncrement P T γ) (ball 0 1) :=
  (matrixRealTraceBanachCLM P T γ).contDiff.comp_contDiffOn (logIncrement_contDiffOn _)

theorem matrixTraceLogRemainder_contDiffOn :
    ContDiffOn ℝ ∞ (matrixTraceLogRemainder P T γ) (ball 0 1) :=
  (matrixRealTraceBanachCLM P T γ).contDiff.comp_contDiffOn (logRemainder_contDiffOn _)

theorem matrixTraceLogRemainder_sub_norm_le {r : ℝ} (hr : 0≤r) (hr4 : r≤1/4)
    {u v : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ}
    (hu : ‖u‖≤r) (hv : ‖v‖≤r) :
    ‖matrixTraceLogRemainder P T γ u-matrixTraceLogRemainder P T γ v‖ ≤
      (8*‖matrixRealTraceCLM n‖*r)*‖u-v‖ := by
  change ‖matrixRealTraceBanachCLM P T γ (logRemainder _ u)-
    matrixRealTraceBanachCLM P T γ (logRemainder _ v)‖≤_
  rw [← map_sub]
  exact (matrixRealTraceBanachCLM_norm_le P T γ _).trans
    ((mul_le_mul_of_nonneg_left (logRemainder_sub_norm_le _ hr hr4 hu hv) (norm_nonneg _)).trans_eq (by ring))

theorem matrixTraceLogRemainder_norm_le
    (u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) (hu : ‖u‖≤1/4) :
    ‖matrixTraceLogRemainder P T γ u‖≤8*‖matrixRealTraceCLM n‖*‖u‖^2 :=
  (matrixRealTraceBanachCLM_norm_le P T γ _).trans
    ((mul_le_mul_of_nonneg_left (logRemainder_norm_le _ hu) (norm_nonneg _)).trans_eq (by ring))

theorem matrixTraceLogRemainder_hasFDerivAt
    {u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ} (hu : ‖u‖<1) :
    HasFDerivAt (matrixTraceLogRemainder P T γ)
      ((matrixRealTraceBanachCLM P T γ).comp (fderiv ℝ (logRemainder _) u)) u := by
  have hR := ((logRemainder_contDiffOn
    (LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ)).contDiffAt
      (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using hu))).differentiableAt (by simp)
  exact (matrixRealTraceBanachCLM P T γ).hasFDerivAt.comp u hR.hasFDerivAt

theorem matrixTraceLogRemainder_fderiv_norm_le
    {u : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ} (hu : ‖u‖≤1/8) :
    ‖fderiv ℝ (matrixTraceLogRemainder P T γ) u‖≤16*‖matrixRealTraceCLM n‖*‖u‖ := by
  rw [(matrixTraceLogRemainder_hasFDerivAt P T γ (by linarith : ‖u‖<1)).fderiv]
  exact ((matrixRealTraceBanachCLM P T γ).opNorm_comp_le _).trans
    ((mul_le_mul (matrixRealTraceBanachCLM_opNorm_le P T γ)
      (logRemainder_fderiv_norm_le _ hu) (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring))

end Yau.LeafProofs.L17Aux
