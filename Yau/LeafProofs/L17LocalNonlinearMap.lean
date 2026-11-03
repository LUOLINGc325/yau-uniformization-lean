import Yau.LeafProofs.L17MatrixLogarithmHolder
import Yau.LeafProofs.L17NormalizedRicciForcing

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
local instance localNonlinearTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)

def normalizedPotentialBudget (A : BoundedChartFamily g) (γ : ℝ) : ℝ :=
  4*inverseMatrixHolderBudget A γ*‖leviHessianCLM n‖

theorem normalizedPotentialBudget_nonneg (A : BoundedChartFamily g) (γ : ℝ) :
    0≤normalizedPotentialBudget A γ := by
  have hB := zero_le_one.trans (inverseMatrixHolderBudget_ge_one A γ)
  unfold normalizedPotentialBudget
  positivity

def localNonlinearMap (u : SchauderSpace P T γ hT) : LocalHolderBanach ℝ P T γ :=
  matrixTraceLogRemainder P T γ (normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u)-
    matrixRealTraceBanachCLM P T γ (timeRicciBanach P hT hTime hγ hγ1 hr)

theorem localNonlinearMap_contDiffAt {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1) :
    ContDiffAt ℝ ∞ (localNonlinearMap P T γ hT hTime hγ hγ1 hr) u :=
  (((matrixTraceLogRemainder_contDiffOn P T γ).contDiffAt
    (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using hu))).comp u
      (normalizedMetricPerturbation_contDiff P T γ hT hTime hγ hγ1 hr).contDiffAt).sub contDiffAt_const

theorem normalizedMetricPerturbation_sub (u v : SchauderSpace P T γ hT) :
    normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u-
      normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr v =
        normalizedPotentialCLM P T γ hT hTime hγ1 hr (u-v) := by
  unfold normalizedMetricPerturbation
  rw [(normalizedPotentialCLM P T γ hT hTime hγ1 hr).map_sub u v]
  abel

theorem localNonlinearMap_sub_norm_le {r : ℝ} (hr0 : 0≤r) (hr4 : r≤1/4)
    {u v : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖≤r)
    (hv : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr v‖≤r) :
    ‖localNonlinearMap P T γ hT hTime hγ hγ1 hr u-
      localNonlinearMap P T γ hT hTime hγ hγ1 hr v‖≤
        (8*‖matrixRealTraceCLM n‖*r*normalizedPotentialBudget P.charts γ)*‖u-v‖ := by
  have hdiff : localNonlinearMap P T γ hT hTime hγ hγ1 hr u-
      localNonlinearMap P T γ hT hTime hγ hγ1 hr v =
      matrixTraceLogRemainder P T γ (normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u)-
      matrixTraceLogRemainder P T γ (normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr v) := by
    unfold localNonlinearMap
    abel
  rw [hdiff]
  have hh := matrixTraceLogRemainder_sub_norm_le P T γ hr0 hr4 hu hv
  rw [normalizedMetricPerturbation_sub P T γ hT hTime hγ hγ1 hr u v] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (normalizedPotentialCLM_norm_le P T γ hT hTime hγ1 hr (u-v))
    (by positivity : 0≤8*‖matrixRealTraceCLM n‖*r)).trans_eq (by unfold normalizedPotentialBudget; ring))

theorem localNonlinearMap_zero_norm_le
    (hF : ‖timeRicciBanach P hT hTime hγ hγ1 hr‖≤1/4) :
    ‖localNonlinearMap P T γ hT hTime hγ hγ1 hr 0‖≤
      3*‖matrixRealTraceCLM n‖*‖timeRicciBanach P hT hTime hγ hγ1 hr‖ := by
  have hz : normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr 0 =
      -timeRicciBanach P hT hTime hγ hγ1 hr := by
    unfold normalizedMetricPerturbation
    rw [(normalizedPotentialCLM P T γ hT hTime hγ1 hr).map_zero,zero_sub]
  have hR := matrixTraceLogRemainder_norm_le P T γ (-timeRicciBanach P hT hTime hγ hγ1 hr)
    (by simpa only [norm_neg] using hF)
  have hL := matrixRealTraceBanachCLM_norm_le P T γ (timeRicciBanach P hT hTime hγ hγ1 hr)
  unfold localNonlinearMap
  rw [hz]
  apply (norm_sub_le _ _).trans
  apply (add_le_add hR hL).trans
  rw [norm_neg]
  have hS : 8*‖timeRicciBanach P hT hTime hγ hγ1 hr‖^2+
      ‖timeRicciBanach P hT hTime hγ hγ1 hr‖≤3*‖timeRicciBanach P hT hTime hγ hγ1 hr‖ := by
    nlinarith [mul_nonneg (norm_nonneg (timeRicciBanach P hT hTime hγ hγ1 hr)) (sub_nonneg.mpr hF)]
  exact (show 8*‖matrixRealTraceCLM n‖*‖timeRicciBanach P hT hTime hγ hγ1 hr‖^2+
      ‖matrixRealTraceCLM n‖*‖timeRicciBanach P hT hTime hγ hγ1 hr‖ =
      ‖matrixRealTraceCLM n‖*(8*‖timeRicciBanach P hT hTime hγ hγ1 hr‖^2+
      ‖timeRicciBanach P hT hTime hγ hγ1 hr‖) by ring).le.trans
    ((mul_le_mul_of_nonneg_left hS (norm_nonneg _)).trans_eq (by ring))

end Yau.LeafProofs.L17Aux
