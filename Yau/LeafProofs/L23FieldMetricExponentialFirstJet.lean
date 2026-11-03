import Yau.LeafProofs.L23FieldMetricVariationLocal

/-! The actual exponential endpoint has its true first fiber derivative in every chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem fieldExp_chart_hasFDerivAt_zero
    (h : HermitianField M) (hh : MetricSmooth h) (x c : M.Carrier)
    (hc : x ∈ (chartAt (ComplexVector n) c).source)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    HasFDerivAt (fun v => chartPt c (fieldExp h x (L v))) ((realTangentCoords c x).comp L) 0 := by
  obtain ⟨B,ρ,ε,X,e,H⟩ := exists_fieldNormalEndpointData h hh x Set.univ isOpen_univ (Set.mem_univ _)
  rcases H with ⟨hB,hxB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  have Hfull : FieldNormalEndpointData h x Set.univ B ρ ε X e :=
    ⟨hB,hxB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let C := (realTangentCoords x x).comp L
  have HC : HasFDerivAt (fun v => X (chartPt x x,C v) 1) C 0 := by
    have HD : HasFDerivAt (fun v => X (chartPt x x,v) 1) (ContinuousLinearMap.id ℝ (ComplexVector n)) (C 0) := by
      simpa only [map_zero] using (hzero _ hxB).2
    convert! HD.comp 0 C.hasFDerivAt using 1
  have h1 : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have HX0 : X (chartPt x x,C 0) 1 = chartPt x x := by rw [map_zero]; exact (hzero _ hxB).1 1 h1
  have hxinv : chartInv x (chartPt x x) = x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hcx : chartInv x (chartPt x x) ∈ (extChartAt (ComplexModel n) c).source := by rw [hxinv]; simpa only [extChartAt_source] using hc
  have Hψ : HasFDerivAt (realChartChange x c) (fderiv ℝ (realChartChange x c) (chartPt x x)) (chartPt x x) :=
    ((realChartChange_contDiffAt x c (mem_extChartAt_target x) hcx).differentiableAt (by simp)).hasFDerivAt
  rw [← HX0] at Hψ
  have Hchain := Hψ.comp 0 HC
  have Hlinear : (fderiv ℝ (realChartChange x c) (X (chartPt x x,C 0) 1)).comp C = (realTangentCoords c x).comp L := by
    rw [HX0,← realTangentCoords_comp_realFrameCLM_change x c x (mem_chart_source _ _) hc]
    dsimp only [C]
    rw [ContinuousLinearMap.comp_assoc,← ContinuousLinearMap.comp_assoc (realFrameCLM x x),
      realFrameCLM_comp_realTangentCoords x x (mem_chart_source _ _),ContinuousLinearMap.id_comp]
  rw [Hlinear] at Hchain
  have Hnear : ∀ᶠ v in 𝓝 (0 : ComplexVector n), C v ∈ Metric.ball 0 ρ :=
    C.continuous.continuousAt.preimage_mem_nhds (by simpa only [map_zero] using Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  apply Hchain.congr_of_eventuallyEq
  filter_upwards [Hnear] with v hv
  have hp : (chartPt x x,realTangentCoords x x (L v)) ∈ e.source := by rw [hsource]; exact ⟨hxB,hv⟩
  rw [fieldExp_normal_coordinates h hh x x Set.univ B ρ ε X e Hfull (mem_chart_source _ _) (L v) hp]
  rfl

theorem parallelExpVariation_chart_firstJet
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (c : M.Carrier) (u : ℝ) (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :
    HasFDerivAt (fun v => chartPt c (parallelExpVariation h γ P u v))
      (u • ((realTangentCoords c (γ u)).comp (P u))) 0 := by
  simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_smul,parallelExpVariation] using
    fieldExp_chart_hasFDerivAt_zero h hh (γ u) c hc (u • P u)

end Yau.LeafProofs.L23Aux
