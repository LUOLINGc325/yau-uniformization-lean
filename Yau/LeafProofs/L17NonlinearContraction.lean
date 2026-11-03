import Yau.LeafProofs.L17GlobalNonlinearMap
import Yau.LeafProofs.L17BanachContraction

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux L17BanachContractionAux
local instance nonlinearContractionTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)
local instance nonlinearContractionAddGroup : AddCommGroup (SchauderSpace P T γ hT) :=
  (schauderSpace_normedAddCommGroup P T γ hT).toAddCommGroup
local instance nonlinearContractionSpace : NormedSpace ℝ (SchauderSpace P T γ hT) :=
  schauderSpace_normedSpace P T γ hT

theorem normalizedMetricPerturbation_norm_le_on_ball {R δ : ℝ}
    (hBudget : normalizedPotentialBudget P.charts γ*R+
      (2*normalizedRicciBudget P.charts γ)*T^(1-γ/2)≤δ)
    {u : SchauderSpace P T γ hT} (hu : ‖u‖≤R) :
    ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖≤δ :=
  (normalizedMetricPerturbation_norm_le P T γ hT hTime hγ hγ1 hr u).trans
    ((add_le_add (mul_le_mul_of_nonneg_left hu
      (normalizedPotentialBudget_nonneg P.charts γ)) (le_refl _)).trans hBudget)

theorem timeRicciBanach_norm_le_of_ball_budget {R δ : ℝ} (hR : 0≤R)
    (hBudget : normalizedPotentialBudget P.charts γ*R+
      (2*normalizedRicciBudget P.charts γ)*T^(1-γ/2)≤δ) :
    ‖timeRicciBanach P hT hTime hγ hγ1 hr‖≤δ := by
  apply (timeRicciBanach_norm_le P hT hTime hγ hγ1 hr).trans
  exact (le_add_of_nonneg_left (mul_nonneg (normalizedPotentialBudget_nonneg P.charts γ) hR)).trans hBudget

theorem globalNonlinearMap_exists_unique_ball_solution
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (e : SchauderSpace P T γ hT ≃L[ℝ] HolderSpace P T γ)
    {R δ : ℝ} (hR : 0≤R) (hδ : 0≤δ) (hδ4 : δ≤1/4)
    (hBudget : normalizedPotentialBudget P.charts γ*R+
      (2*normalizedRicciBudget P.charts γ)*T^(1-γ/2)≤δ)
    (hContract : ‖e.symm.toContinuousLinearMap‖*
      (4*‖J‖*‖matrixRealTraceCLM n‖*δ*normalizedPotentialBudget P.charts γ)≤1/2)
    (hZero : ‖e.symm.toContinuousLinearMap‖*
      ((3*‖J‖*‖matrixRealTraceCLM n‖*normalizedRicciBudget P.charts γ)*T^(1-γ/2))≤R/2) :
    ∃! u : SchauderSpace P T γ hT, ‖u‖≤R ∧
      e u=globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u := by
  let N := globalNonlinearMap P T γ hT hTime hγ hγ1 hr J
  let L := 4*‖J‖*‖matrixRealTraceCLM n‖*δ*normalizedPotentialBudget P.charts γ
  have hLip (u v : SchauderSpace P T γ hT) (hu : ‖u‖≤R) (hv : ‖v‖≤R) :
      ‖N u-N v‖≤L*‖u-v‖ :=
    globalNonlinearMap_sub_norm_le P T γ hT hTime hγ hγ1 hr J hδ hδ4
      (normalizedMetricPerturbation_norm_le_on_ball P T γ hT hTime hγ hγ1 hr hBudget hu)
      (normalizedMetricPerturbation_norm_le_on_ball P T γ hT hTime hγ hγ1 hr hBudget hv)
  have hF : ‖timeRicciBanach P hT hTime hγ hγ1 hr‖≤1/4 :=
    (timeRicciBanach_norm_le_of_ball_budget P T γ hT hTime hγ hγ1 hr hR hBudget).trans hδ4
  have hZ : ‖e.symm ((0 : HolderSpace P T γ)+N 0)‖≤R/2 := by
    simp only [zero_add]
    exact (e.symm.toContinuousLinearMap.le_opNorm (N 0)).trans
      ((mul_le_mul_of_nonneg_left
        (globalNonlinearMap_zero_norm_le P T γ hT hTime hγ hγ1 hr J hF)
        (norm_nonneg _)).trans hZero)
  simpa only [zero_add] using exists_unique_ball_solution e 0 N R L hR hLip hContract hZ

end Yau.LeafProofs.L17Aux
