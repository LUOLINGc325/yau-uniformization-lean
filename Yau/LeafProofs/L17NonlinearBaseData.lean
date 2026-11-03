import Yau.LeafProofs.L17NonlinearControlledBall
import Yau.LeafProofs.L17NonlinearScales
import Yau.LeafProofs.L17NonlinearEmbedding

open Set Metric
open scoped Matrix Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17LocalScalarAssemblyAux
open L17NonlinearEmbeddingAux
local instance nonlinearBaseTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def NonlinearBaseAt (P : UniformChartPartition g) (T : ℝ) (hT : 0<T)
    (hTime : T≤P.radius^2) (hr : P.radius≤1) : Prop :=
  ∃ Ja : LocalHolderSpace ℝ P T (1/2) →L[ℝ] HolderSpace P T (1/2),
  ∃ Jb : LocalHolderSpace ℝ P T (1/4) →L[ℝ] HolderSpace P T (1/4),
    (∀ v,holderFun (Ja v)=scalarAssemblyFunction P v) ∧
    (∀ v,holderFun (Jb v)=scalarAssemblyFunction P v) ∧
    ∃ ua : SchauderSpace P T (1/2) hT, ∃ ub : SchauderSpace P T (1/4) hT,
      scalarParabolicCLM P T (1/2) hT hTime (by norm_num) hr ua=
        globalNonlinearMap P T (1/2) hT hTime (by norm_num) (by norm_num) hr Ja ua ∧
      scalarParabolicCLM P T (1/4) hT hTime (by norm_num) hr ub=
        globalNonlinearMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr Jb ub ∧
      schauderFun ua=schauderFun ub ∧
      ‖normalizedMetricPerturbation P T (1/2) hT hTime (by norm_num) (by norm_num) hr ua‖<1 ∧
      ‖normalizedMetricPerturbation P T (1/4) hT hTime (by norm_num) (by norm_num) hr ub‖<1 ∧
      ‖ua‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹ ∧
      ‖ub‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹ ∧
      ∃ B0 : SchauderSpace P T (1/4) hT ≃L[ℝ] HolderSpace P T (1/4),
        B0.toContinuousLinearMap=fderiv ℝ
          (scalarNonlinearResidualMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr Jb) ub

theorem exists_nonlinear_base_of_scalar_isomorphisms
    (P : UniformChartPartition g) (hg : MetricSmooth g) (hr : P.radius≤1)
    (hρ : 2*P.radius<P.charts.radius) (Cw : ℝ) (hCw : 1≤Cw)
    (hDeriv : ∀ (p : P.centers) (q : M.Carrier) z,z∈ball (0 : ComplexVector n) (2*P.radius) →
      ‖fderiv ℝ (fun w => P.weight p (P.charts.chart q w)) z‖≤Cw/P.radius)
    (Ca Cb τ : ℝ) (hτ : 0<τ)
    (hIso : ∀ (T : ℝ) (hT : 0<T),T≤τ → ∃ hTime : T≤P.radius^2,
      ∃ ea : SchauderSpace P T (1/2) hT ≃L[ℝ] HolderSpace P T (1/2),
      ∃ eb : SchauderSpace P T (1/4) hT ≃L[ℝ] HolderSpace P T (1/4),
        ea.toContinuousLinearMap=scalarParabolicCLM P T (1/2) hT hTime (by norm_num) hr ∧
        eb.toContinuousLinearMap=scalarParabolicCLM P T (1/4) hT hTime (by norm_num) hr ∧
        ‖ea.symm.toContinuousLinearMap‖≤Ca ∧ ‖eb.symm.toContinuousLinearMap‖≤Cb) :
    ∃ T : ℝ, ∃ hT : 0<T, T≤τ ∧ ∃ hTime : T≤P.radius^2,NonlinearBaseAt P T hT hTime hr := by
  obtain ⟨Cja,hCja,hAssemblya⟩ := exists_uniform_local_scalar_assembly P.charts hg P.overlapBudget
    Cw (1/2 : ℝ) hCw (by norm_num) (by norm_num)
  obtain ⟨Cjb,hCjb,hAssemblyb⟩ := exists_uniform_local_scalar_assembly P.charts hg P.overlapBudget
    Cw (1/4 : ℝ) hCw (by norm_num) (by norm_num)
  let b : Fin 10 → ℝ := ![Ca,Cb,Cja,Cjb,‖matrixRealTraceCLM n‖,
    normalizedPotentialBudget P.charts (1/2),normalizedPotentialBudget P.charts (1/4),
    normalizedRicciBudget P.charts (1/2),normalizedRicciBudget P.charts (1/4),
    backgroundLogDetHessianBudget P.charts]
  let K := max (3:ℝ) (∑ i : Fin 10,|b i|)
  have hK3 : 3≤K := le_max_left _ _
  have hK : 1≤K := (by norm_num : (1:ℝ)≤3).trans hK3
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hCap (i : Fin 10) : b i≤K := (le_abs_self _).trans
    ((Finset.single_le_sum (fun j (_ : j∈Finset.univ) => abs_nonneg (b j)) (Finset.mem_univ i)).trans
      (le_max_right _ _))
  have hCaK : Ca≤K := hCap 0
  have hCbK : Cb≤K := hCap 1
  have hCjaK : Cja≤K := hCap 2
  have hCjbK : Cjb≤K := hCap 3
  have hTrK : ‖matrixRealTraceCLM n‖≤K := hCap 4
  have hPaK : normalizedPotentialBudget P.charts (1/2)≤K := hCap 5
  have hPbK : normalizedPotentialBudget P.charts (1/4)≤K := hCap 6
  have hRaK : normalizedRicciBudget P.charts (1/2)≤K := hCap 7
  have hRbK : normalizedRicciBudget P.charts (1/4)≤K := hCap 8
  have hBgK : backgroundLogDetHessianBudget P.charts≤K := hCap 9
  obtain ⟨δ,Ra,Rb,σ,hδ,hδ8,hRa,hRb,hσ,hσ1,hDelta,hKRb,hKRa,hRbEll,hTimes⟩ :=
    exists_common_nonlinear_scales hK (inv_pos.mpr (P.charts.bound_pos 0))
  have hRaRb : Ra≤Rb := by
    have h := mul_le_mul_of_nonneg_right hK hRa.le
    nlinarith
  let T := min τ (σ^2)/2
  have hT : 0<T := div_pos (lt_min hτ (sq_pos_of_pos hσ)) (by norm_num)
  have hTτ : T≤τ := by dsimp only [T]; have := min_le_left τ (σ^2); linarith
  have hTσ : T≤σ^2 := by dsimp only [T]; have := min_le_right τ (σ^2); nlinarith [sq_nonneg σ]
  obtain ⟨hTime,ea,eb,hea,heb,heaNorm,hebNorm⟩ := hIso T hT hTτ
  obtain ⟨Ja,hJaNorm,hJa,_⟩ := hAssemblya P rfl le_rfl hr hρ hDeriv T hT.le hTime
  obtain ⟨Jb,hJbNorm,hJb,_⟩ := hAssemblyb P rfl le_rfl hr hρ hDeriv T hT.le hTime
  obtain ⟨_,hTimeΔa,hTime0a,hTimePSD⟩ := hTimes T hT hTσ (1-(1/2 : ℝ)/2) (by norm_num)
  obtain ⟨_,hTimeΔb,hTime0b,_⟩ := hTimes T hT hTσ (1-(1/4 : ℝ)/2) (by norm_num)
  obtain ⟨ua,huaNorm,huaEq,huaZ,huaPSD,huaD,_⟩ := exists_controlled_nonlinear_ball_solution
    P T (1/2) hT hTime (by norm_num) (by norm_num) hr Ja ea hea hK hδ hδ8 hRa le_rfl hRaRb
      (heaNorm.trans hCaK) (hJaNorm.trans hCjaK) hTrK hPaK hRaK hBgK hDelta hKRb hTimeΔa hTime0a hTimePSD
  obtain ⟨ub,hubNorm,hubEq,hubZ,hubPSD,hubD,hubUnique⟩ := exists_controlled_nonlinear_ball_solution
    P T (1/4) hT hTime (by norm_num) (by norm_num) hr Jb eb heb hK hδ hδ8 hRa hRaRb le_rfl
      (hebNorm.trans hCbK) (hJbNorm.trans hCjbK) hTrK hPbK hRbK hBgK hDelta hKRb hTimeΔb hTime0b hTimePSD
  have huaZ1 := huaZ.trans_lt (hδ8.trans_lt (by norm_num : (1/8 : ℝ)<1))
  have hubZ1 := hubZ.trans_lt (hδ8.trans_lt (by norm_num : (1/8 : ℝ)<1))
  let v := schauderWeakenCLM P hT hTime (by norm_num : (1/4 : ℝ)≤1/2) ua
  have hWeakenPower : (3:ℝ)^((1/2 : ℝ)-1/4)≤3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (by norm_num : (1/2 : ℝ)-1/4≤1)
    simpa only [Real.rpow_one] using h
  have hvNorm : ‖v‖≤Rb := by
    have h := schauderWeakenElement_norm_le P hTime (by norm_num : (1/4 : ℝ)≤1/2) ua
    change ‖v‖≤(3:ℝ)^((1/2 : ℝ)-1/4)*‖ua‖ at h
    exact (h.trans (mul_le_mul (hWeakenPower.trans hK3) huaNorm (norm_nonneg _) hK0.le)).trans
      (hKRa.trans (by linarith))
  have hBbudget : normalizedPotentialBudget P.charts (1/4)*Rb+
      (2*normalizedRicciBudget P.charts (1/4))*T^(1-(1/4 : ℝ)/2)≤δ := by
    have hOne := mul_le_mul_of_nonneg_right hPbK hRb.le
    have hTwo : (2*normalizedRicciBudget P.charts (1/4))*T^(1-(1/4 : ℝ)/2)≤2*K*T^(1-(1/4 : ℝ)/2) := by
      gcongr
    linarith
  have hvZ := normalizedMetricPerturbation_norm_le_on_ball P T (1/4) hT hTime
    (by norm_num) (by norm_num) hr hBbudget hvNorm
  have hvPSD : ‖v‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hBgK hT.le
    have hEll := (inv_pos.mpr (P.charts.bound_pos 0)).le
    nlinarith
  have hN := globalNonlinearMap_weaken hg hTime (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)≤1) (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1/2)
    hr Ja Jb hJa hJb ua huaZ1 (hvZ.trans_lt (hδ8.trans_lt (by norm_num))) huaPSD hvPSD
  have hP := congrArg (fun L => L ua) (scalarParabolic_weaken P hT hTime
    (by norm_num : (1/2:ℝ)≤1) (by norm_num : (1/4:ℝ)≤1/2) hr)
  simp only [ContinuousLinearMap.comp_apply] at hP
  have hvEq : scalarParabolicCLM P T (1/4) hT hTime (by norm_num) hr v=
      globalNonlinearMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr Jb v := by
    rw [hP,huaEq,hN]
  have hvub : v=ub := hubUnique v hvNorm hvEq
  have huv : schauderFun ua=schauderFun ub :=
    (schauderWeakenCLM_function P hT hTime (by norm_num : (1/4:ℝ)≤1/2) ua).symm.trans
      (congrArg schauderFun hvub)
  obtain ⟨B0,hB0,_⟩ := exists_scalarNonlinearResidual_linearization P T (1/4) hT hTime
    (by norm_num) (by norm_num) hr Jb eb heb hubZ1 hubD
  exact ⟨T,hT,hTτ,hTime,Ja,Jb,hJa,hJb,ua,ub,huaEq,hubEq,huv,huaZ1,hubZ1,huaPSD,hubPSD,B0,hB0⟩

end Yau.LeafProofs.L17Aux
