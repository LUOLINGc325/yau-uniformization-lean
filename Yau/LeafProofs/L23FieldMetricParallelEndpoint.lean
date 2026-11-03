import Yau.LeafProofs.L23FieldMetricFrameEquiv

/-! Genuine parallel transport normalized to the actual preferred frame at the final endpoint. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000

theorem parallelFrameOn_comp_const
    (h : HermitianField M) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (I : Set ℝ) (HP : IsParallelFrameOn h γ P I)
    (L : ComplexVector n →L[ℝ] ComplexVector n) :
    IsParallelFrameOn h γ (fun u => (P u).comp L) I := by
  intro c t ht hc
  have H := (HP c t ht hc).clm_comp (hasDerivAt_const t L)
  simpa only [ContinuousLinearMap.comp_zero,add_zero,ContinuousLinearMap.comp_assoc] using H

theorem exists_endpoint_parallel_frame
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (J : Set ℝ) (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J →
    ∃ δ : ℝ, 0 < δ ∧
      ∃ P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u),
        (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1) ∧
        Set.Ioo (-δ) (1+δ) ⊆ J ∧
        IsParallelFrameOn h γ (fun u => (P u).toContinuousLinearMap) (Set.Ioo (-δ) (1+δ)) ∧
        ∀ u ∈ Set.Ioo (-δ) (1+δ), ∀ v w : ComplexVector n,
          (underlyingRealRiemannianMetric h).inner (γ u) (P u v) (P u w) =
            realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) v w := by
  letI := manifold_realSmooth M
  intro hγ
  classical
  obtain ⟨δ,hδ,R,hR0,hsub,HR⟩ := exists_parallel_frame_unit h hh γ J hJ hunit hγ (realFrameCLM (γ 0) (γ 0))
  let I := Set.Ioo (-δ) (1+δ)
  have h0 : (0 : ℝ) ∈ I := by constructor <;> linarith
  have h1 : (1 : ℝ) ∈ I := by constructor <;> linarith
  have Hpair (u : ℝ) (hu : u ∈ I) (v w : ComplexVector n) :
      (underlyingRealRiemannianMetric h).inner (γ u) (R u v) (R u w) =
        realMetricInChart h (γ 0) (chartPt (γ 0) (γ 0)) v w := by
    have H := parallelFrame_pairing_constant h hh γ R (-δ) (1+δ) HR (hγ.mono hsub) u 0 hu h0 v w
    rw [hR0] at H
    have HM := realMetricInChart_tangentCoords h (γ 0) (γ 0) (mem_chart_source _ _)
      (realFrameCLM (γ 0) (γ 0) v) (realFrameCLM (γ 0) (γ 0) w)
    simp only [realTangentCoords_realFrameCLM _ _ (mem_chart_source _ _)] at HM
    exact H.trans HM.symm
  have hinj (u : ℝ) (hu : u ∈ I) : Function.Injective (R u) :=
    physical_frame_pairing_injective h (γ 0) (γ u) (R u) (Hpair u hu)
  let Q : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u) :=
    fun u => if hu : u ∈ I then frameEquivOfInjective (γ u) (R u) (hinj u hu) else realFrameEquiv (γ u)
  have hQ (u : ℝ) (hu : u ∈ I) : (Q u).toContinuousLinearMap = R u := by
    dsimp only [Q]
    rw [dif_pos hu]
    exact frameEquivOfInjective_toContinuousLinearMap _ _ _
  let L := (realFrameEquiv (γ 1)).trans (Q 1).symm
  let P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u) :=
    fun u => L.trans (Q u)
  have hP (u : ℝ) (hu : u ∈ I) : (P u).toContinuousLinearMap = (R u).comp L.toContinuousLinearMap := by
    change (Q u).toContinuousLinearMap.comp L.toContinuousLinearMap = _
    rw [hQ u hu]
  have HP : IsParallelFrameOn h γ (fun u => (P u).toContinuousLinearMap) I := by
    intro c t ht hc
    have H := parallelFrameOn_comp_const h γ R I HR L.toContinuousLinearMap c t ht hc
    have HEq : (fun u => (realTangentCoords c (γ u)).comp (P u).toContinuousLinearMap) =ᶠ[𝓝 t]
        (fun u => (realTangentCoords c (γ u)).comp ((R u).comp L.toContinuousLinearMap)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      rw [hP u hu]
    change HasDerivAt (fun u => (realTangentCoords c (γ u)).comp (P u).toContinuousLinearMap)
      ((chartParallelCoefficient h c γ t).comp ((realTangentCoords c (γ t)).comp (P t).toContinuousLinearMap)) t
    rw [hP t ht]
    exact H.congr_of_eventuallyEq HEq
  have hP1 : (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1) := by
    ext v
    change Q 1 ((Q 1).symm (realFrameEquiv (γ 1) v)) = realFrameCLM (γ 1) (γ 1) v
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun F : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ 1) => F v)
      (realFrameEquiv_toContinuousLinearMap _)
  refine ⟨δ,hδ,P,hP1,hsub,HP,?_⟩
  intro u hu v w
  have H := parallelFrame_pairing_constant h hh γ (fun s => (P s).toContinuousLinearMap)
    (-δ) (1+δ) HP (hγ.mono hsub) u 1 hu h1 v w
  change (underlyingRealRiemannianMetric h).inner (γ u) (P u v) (P u w) =
    (underlyingRealRiemannianMetric h).inner (γ 1) ((P 1).toContinuousLinearMap v) ((P 1).toContinuousLinearMap w) at H
  rw [hP1] at H
  have HM := realMetricInChart_tangentCoords h (γ 1) (γ 1) (mem_chart_source _ _)
    (realFrameCLM (γ 1) (γ 1) v) (realFrameCLM (γ 1) (γ 1) w)
  simp only [realTangentCoords_realFrameCLM _ _ (mem_chart_source _ _)] at HM
  exact H.trans HM.symm

end Yau.LeafProofs.L23Aux
