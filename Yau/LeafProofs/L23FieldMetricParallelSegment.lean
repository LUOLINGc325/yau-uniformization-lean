import Yau.LeafProofs.L23FieldMetricParallelFromChart
import Yau.LeafProofs.L23FieldMetricParallelInterval

/-! Actual parallel frames on one compact coordinate segment, with prescribed initial frame. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem exists_parallel_frame_segment
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (c : M.Carrier) (J : Set ℝ) (hJ : IsOpen J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J →
    Set.MapsTo γ J (chartAt (ComplexVector n) c).source →
    ∀ (a b : ℝ), a < b → Set.Icc a b ⊆ J →
    ∀ F : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ a),
    ∃ δ : ℝ, 0 < δ ∧
      ∃ P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u),
        P a = F ∧ Set.Ioo (a-δ) (b+δ) ⊆ J ∧
        IsParallelFrameOn h γ P (Set.Ioo (a-δ) (b+δ)) := by
  letI := manifold_realSmooth M
  intro hγ hsource a b hab hsegment F
  let C := (realTangentCoords c (γ a)).comp F
  obtain ⟨δ,hδ,W,hWa,hW,hsol⟩ :=
    exists_chart_parallel_matrix_interval h hh γ c J hJ hγ hsource a b hab hsegment C
  let P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u) :=
    fun u => (realFrameCLM c (γ u)).comp (W u)
  have hsub : Set.Ioo (a-δ) (b+δ) ⊆ J := fun t ht => (hsol t ht).1
  refine ⟨δ,hδ,P,?_,hsub,?_⟩
  · change (realFrameCLM c (γ a)).comp (W a) = F
    rw [hWa]
    dsimp only [C]
    rw [← ContinuousLinearMap.comp_assoc,
      realFrameCLM_comp_realTangentCoords c (γ a) (hsource (hsegment ⟨le_rfl,hab.le⟩)),
      ContinuousLinearMap.id_comp]
  · exact parallelFrameOn_of_chart_matrix h hh γ c _ isOpen_Ioo W
      (hγ.mono hsub) (fun t ht => hsource (hsub ht)) (fun t ht => (hsol t ht).2.1)

end Yau.LeafProofs.L23Aux
