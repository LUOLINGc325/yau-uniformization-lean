import Yau.LeafProofs.L17LocalScalarAssemblyCompatibility

open Set Metric
open scoped Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalScalarAssemblyAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem exists_uniform_scalar_assembly_elements (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (N : ℕ) (Cw γ : ℝ) (hCw : 1 ≤ Cw) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : UniformChartPartition g), P.charts=A → P.overlapBudget ≤ N →
      P.radius ≤ 1 → 2*P.radius < A.radius →
      (∀ (p : P.centers) (q : M.Carrier) z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
        ‖fderiv ℝ (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ Cw/P.radius) →
      ∀ (T : ℝ), 0 ≤ T → T ≤ P.radius^2 → ∀ (u : LocalHolderSpace ℝ P T γ),
        ∃ v : HolderSpace P T γ, holderFun v=scalarAssemblyFunction P u ∧ ‖v‖ ≤ C*‖u‖ := by
  obtain ⟨Craw,hCraw,hRaw⟩ := exists_uniform_raw_sum_holder A hg N γ hγ0.le
  let D := scalarAssemblyLocalBudget Cw γ
  have hCw0 : 0 ≤ Cw := zero_le_one.trans hCw
  have hD0 : 0 ≤ D := scalarAssemblyLocalBudget_nonneg hCw0
  refine ⟨Craw*(1+D),mul_pos hCraw (by linarith),?_⟩
  intro P hPA hPN hρone hρr hDeriv T hT hTime u
  obtain ⟨v,hv,_⟩ := hRaw P hPA hPN hρone hρr T ‖u‖ (D*‖u‖) (norm_nonneg u)
    (mul_nonneg hD0 (norm_nonneg u)) (weightedLocalFunction P u)
    (fun p => (weightedLocalFunction_continuous P u p).continuousOn)
    (weightedLocalFunction_zero_outside P u)
    (fun p z _ t => weightedLocalFunction_abs_le P u p (z,t))
    (fun p z w _ _ t s => weightedLocalFunction_difference P hTime hγ0.le hγ1.le hCw0 hDeriv u p (z,t) (w,s))
  refine ⟨v,?_,?_⟩
  · rw [hv.1]
    funext q
    apply finsum_congr
    intro p
    exact rawLocalizedTerm_weighted_eq P u p q
  · exact hv.2.trans_eq (by ring)

theorem exists_uniform_local_scalar_assembly (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (N : ℕ) (Cw γ : ℝ) (hCw : 1 ≤ Cw) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : UniformChartPartition g), P.charts=A → P.overlapBudget ≤ N →
      P.radius ≤ 1 → 2*P.radius < A.radius →
      (∀ (p : P.centers) (q : M.Carrier) z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
        ‖fderiv ℝ (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ Cw/P.radius) →
      ∀ (T : ℝ), 0 ≤ T → T ≤ P.radius^2 →
        ∃ J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ,
          ‖J‖ ≤ C ∧ (∀ u, holderFun (J u)=scalarAssemblyFunction P u) ∧
          ∀ (u : LocalHolderSpace ℝ P T γ) (F : Cylinder M T → ℝ),
            (∀ (p : P.centers) (zt : ChartCylinder P T), localFun ℝ u ⟨p,zt⟩=F (chartPoint P T p zt)) →
            holderFun (J u)=F ∧ Continuous F := by
  obtain ⟨C,hC,hElements⟩ := exists_uniform_scalar_assembly_elements A hg N Cw γ hCw hγ0 hγ1
  refine ⟨C,hC,?_⟩
  intro P hPA hPN hρone hρr hDeriv T hT hTime
  choose F hF hFNorm using hElements P hPA hPN hρone hρr hDeriv T hT hTime
  let L : LocalHolderSpace ℝ P T γ →ₗ[ℝ] HolderSpace P T γ := {
    toFun := F
    map_add' := fun u v => by
      apply holderFun_injective P T γ
      funext q
      change holderFun (F (u+v)) q=holderFun (F u) q+holderFun (F v) q
      rw [hF (u+v),hF u,hF v,scalarAssemblyFunction_add]
      rfl
    map_smul' := fun c u => by
      apply holderFun_injective P T γ
      funext q
      change holderFun (F (c • u)) q=c*holderFun (F u) q
      rw [hF (c • u),hF u,scalarAssemblyFunction_smul]
      rfl }
  let J := L.mkContinuous C hFNorm
  have hValue (u : LocalHolderSpace ℝ P T γ) : holderFun (J u)=scalarAssemblyFunction P u := hF u
  refine ⟨J,ContinuousLinearMap.opNorm_le_bound J hC.le hFNorm,hValue,?_⟩
  intro u f hf
  have heq : holderFun (J u)=f := (hValue u).trans (scalarAssemblyFunction_of_compatible P u f hf)
  refine ⟨heq,?_⟩
  rw [← heq]
  exact (J u).val.1.continuous

end Yau.LeafProofs.L17LocalScalarAssemblyAux
