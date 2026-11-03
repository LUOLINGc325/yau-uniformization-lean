import Yau.LeafProofs.L17NonlinearContraction
import Yau.LeafProofs.L17NonlinearResidual

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
local instance controlledBallTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)

theorem normalizedRicciBudget_nonneg (A : BoundedChartFamily g) (a : ℝ) :
    0≤normalizedRicciBudget A a := by
  have hi := zero_le_one.trans (inverseMatrixHolderBudget_ge_one A a)
  have hb := zero_le_one.trans (backgroundLogDetHessianBudget_ge_one A)
  unfold normalizedRicciBudget ricciMatrixHolderBudget
  positivity

theorem exists_controlled_nonlinear_ball_solution
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (e : SchauderSpace P T γ hT ≃L[ℝ] HolderSpace P T γ)
    (he : e.toContinuousLinearMap=scalarParabolicCLM P T γ hT hTime hγ1 hr)
    {K δ Ra Rb R : ℝ} (hK : 1≤K) (hδ : 0<δ) (hδ8 : δ≤1/8)
    (hRa : 0<Ra) (hRalo : Ra≤R) (hRhi : R≤Rb)
    (heK : ‖e.symm.toContinuousLinearMap‖≤K) (hJK : ‖J‖≤K)
    (hTrK : ‖matrixRealTraceCLM n‖≤K)
    (hPK : normalizedPotentialBudget P.charts γ≤K)
    (hRK : normalizedRicciBudget P.charts γ≤K)
    (hBgK : backgroundLogDetHessianBudget P.charts≤K)
    (hDelta : 8*K^4*δ≤1/4) (hRb : K*Rb≤δ/4)
    (hTimeDelta : 2*K*T^(1-γ/2)≤δ/4)
    (hTimeZero : 3*K^4*T^(1-γ/2)≤Ra/4)
    (hTimePSD : Rb+K*T≤(P.charts.bound 0)⁻¹/2) :
    ∃ u : SchauderSpace P T γ hT, ‖u‖≤R ∧
      scalarParabolicCLM P T γ hT hTime hγ1 hr u=globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u ∧
      ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖≤δ ∧
      ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹ ∧
      ‖e.symm.toContinuousLinearMap‖*‖fderiv ℝ (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J) u‖≤1/4 ∧
      ∀ v : SchauderSpace P T γ hT, ‖v‖≤R →
        scalarParabolicCLM P T γ hT hTime hγ1 hr v=globalNonlinearMap P T γ hT hTime hγ hγ1 hr J v → v=u := by
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hR : 0≤R := hRa.le.trans hRalo
  have hRb0 : 0≤Rb := hR.trans hRhi
  have hP0 := normalizedPotentialBudget_nonneg P.charts γ
  have hR0 := normalizedRicciBudget_nonneg P.charts γ
  have hp : 0≤T^(1-γ/2) := Real.rpow_nonneg hT.le _
  have hBudget : normalizedPotentialBudget P.charts γ*R+
      (2*normalizedRicciBudget P.charts γ)*T^(1-γ/2)≤δ := by
    have hOne : normalizedPotentialBudget P.charts γ*R≤K*Rb := mul_le_mul hPK hRhi hR hK0.le
    have hTwo : (2*normalizedRicciBudget P.charts γ)*T^(1-γ/2)≤2*K*T^(1-γ/2) := by gcongr
    linarith
  have hContract : ‖e.symm.toContinuousLinearMap‖*
      (4*‖J‖*‖matrixRealTraceCLM n‖*δ*normalizedPotentialBudget P.charts γ)≤1/2 := by
    have h := calc
      ‖e.symm.toContinuousLinearMap‖*(4*‖J‖*‖matrixRealTraceCLM n‖*δ*normalizedPotentialBudget P.charts γ)
          ≤ K*(4*K*K*δ*K) := by gcongr
      _ = 4*K^4*δ := by ring
    linarith
  have hZero : ‖e.symm.toContinuousLinearMap‖*
      ((3*‖J‖*‖matrixRealTraceCLM n‖*normalizedRicciBudget P.charts γ)*T^(1-γ/2))≤R/2 := by
    have h := calc
      ‖e.symm.toContinuousLinearMap‖*((3*‖J‖*‖matrixRealTraceCLM n‖*normalizedRicciBudget P.charts γ)*T^(1-γ/2))
          ≤ K*((3*K*K*K)*T^(1-γ/2)) := by gcongr
      _ = 3*K^4*T^(1-γ/2) := by ring
    linarith
  obtain ⟨u,hu,hUnique⟩ := globalNonlinearMap_exists_unique_ball_solution P T γ hT hTime hγ hγ1 hr
    J e hR hδ.le (hδ8.trans (by norm_num)) hBudget hContract hZero
  have huZ := normalizedMetricPerturbation_norm_le_on_ball P T γ hT hTime hγ hγ1 hr hBudget hu.1
  have heApp (v : SchauderSpace P T γ hT) : e v=scalarParabolicCLM P T γ hT hTime hγ1 hr v :=
    congrArg (fun L : SchauderSpace P T γ hT →L[ℝ] HolderSpace P T γ => L v) he
  refine ⟨u,hu.1,by rw [←heApp];exact hu.2,huZ,?_,?_,?_⟩
  · have hBT : T*backgroundLogDetHessianBudget P.charts≤T*K :=
      mul_le_mul_of_nonneg_left hBgK hT.le
    have hEll := (inv_pos.mpr (P.charts.bound_pos 0)).le
    nlinarith [hu.1]
  · have hD := globalNonlinearMap_fderiv_norm_le P T γ hT hTime hγ hγ1 hr J (huZ.trans hδ8)
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖*
        (8*‖J‖*‖matrixRealTraceCLM n‖*‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖*
          normalizedPotentialBudget P.charts γ) := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      _ ≤ K*(8*K*K*δ*K) := by gcongr
      _ = 8*K^4*δ := by ring
      _ ≤ 1/4 := hDelta
  · intro v hv hEq
    apply hUnique v
    exact ⟨hv,by rw [heApp];exact hEq⟩

end Yau.LeafProofs.L17Aux
