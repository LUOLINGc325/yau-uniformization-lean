import Yau.LeafProofs.L23FieldMetricParallelCalculus
import Yau.LeafProofs.L23FieldMetricLinearODEInterval

/-! Genuine matrix parallel transport on a compact path segment inside one actual chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem exists_chart_parallel_matrix_interval
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (c : M.Carrier) (J : Set ℝ) (hJ : IsOpen J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J →
    Set.MapsTo γ J (chartAt (ComplexVector n) c).source →
    ∀ (a b : ℝ), a < b → Set.Icc a b ⊆ J →
    ∀ C : ComplexVector n →L[ℝ] ComplexVector n,
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ → ComplexVector n →L[ℝ] ComplexVector n,
      W a = C ∧ ContDiffOn ℝ 3 W (Set.Ioo (a-δ) (b+δ)) ∧
      ∀ t ∈ Set.Ioo (a-δ) (b+δ), t ∈ J ∧
        HasDerivAt W ((chartParallelCoefficient h c γ t).comp (W t)) t ∧
        ∀ v w : ComplexVector n, realMetricInChart h c (chartPt c (γ t)) (W t v) (W t w) =
          realMetricInChart h c (chartPt c (γ a)) (C v) (C w) := by
  letI := manifold_realSmooth M
  intro hγ hsource a b hab hsegment C
  have HA := chartParallelCoefficient_contDiffOn_two h hh γ c J hJ hγ hsource
  obtain ⟨δ,hδ,W,hW₀,hW,hsol⟩ := exists_interval_linear_solution (chartParallelCoefficient h c γ) J hJ HA a b hab hsegment C
  have Hcoord := curve_coordinates_contDiffOn_three γ c J hJ hγ hsource
  have haderiv (t : ℝ) (ht : t ∈ Set.Ioo (a-δ) (b+δ)) :
      HasDerivAt (fun u => chartPt c (γ u)) (deriv (fun u => chartPt c (γ u)) t) t :=
    ((Hcoord.contDiffAt (hJ.mem_nhds (hsol t ht).1)).differentiableAt (by norm_num)).hasDerivAt
  have hchart (t : ℝ) (ht : t ∈ Set.Ioo (a-δ) (b+δ)) : chartPt c (γ t) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source
      (by simpa only [extChartAt_source] using hsource (hsol t ht).1)
  have ha : a ∈ Set.Ioo (a-δ) (b+δ) := by constructor <;> linarith
  refine ⟨δ,hδ,W,hW₀,hW,?_⟩
  intro t ht
  refine ⟨(hsol t ht).1,(hsol t ht).2,?_⟩
  intro v w
  have H := chartParallel_matrix_pairing_constant h hh c
    (fun u => chartPt c (γ u)) (fun u => deriv (fun r => chartPt c (γ r)) u) W
    (fun u hu => ⟨hchart u hu,haderiv u hu⟩) (fun u hu => (hsol u hu).2) v w ht ha
  rwa [hW₀] at H

end Yau.LeafProofs.L23Aux
