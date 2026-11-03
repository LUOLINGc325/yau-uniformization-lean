import Yau.LeafProofs.L23FieldMetricParallelFrame

/-! A matrix solution in one genuine chart solves the actual parallel equation in every chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem parallelFrameOn_of_chart_matrix
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (c : M.Carrier) (I : Set ℝ) (hI : IsOpen I)
    (W : ℝ → ComplexVector n →L[ℝ] ComplexVector n) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ I →
    Set.MapsTo γ I (chartAt (ComplexVector n) c).source →
    (∀ t ∈ I, HasDerivAt W ((chartParallelCoefficient h c γ t).comp (W t)) t) →
    IsParallelFrameOn h γ (fun u => (realFrameCLM c (γ u)).comp (W u)) I := by
  letI := manifold_realSmooth M
  intro hγ hsource hW b t ht hb
  have Hcoord := curve_coordinates_contDiffOn_three γ c I hI hγ hsource
  have HD : HasDerivAt (fun u => chartPt c (γ u)) (deriv (fun u => chartPt c (γ u)) t) t :=
    ((Hcoord.contDiffAt (hI.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
  have hcont : ContinuousAt γ t := hγ.continuousOn.continuousAt (hI.mem_nhds ht)
  have HDb := curve_coordinates_change_hasDerivAt γ c b t _ hcont (hsource ht) hb HD
  have hz : chartPt c (γ t) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hsource ht)
  have hinv : chartInv c (chartPt c (γ t)) = γ t :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hsource ht)
  have hyb : chartInv c (chartPt c (γ t)) ∈ (extChartAt (ComplexModel n) b).source := by
    rw [hinv]
    simpa only [extChartAt_source] using hb
  have Hchange := parallel_matrix_change_hasDerivAt h hh c b hz hyb HD (hW t ht)
  have Hpoint : realChartChange c b (chartPt c (γ t)) = chartPt b (γ t) := by
    change chartPt b (chartInv c (chartPt c (γ t))) = chartPt b (γ t)
    rw [hinv]
  rw [Hpoint,← HDb.deriv] at Hchange
  let Z : ℝ → ComplexVector n →L[ℝ] ComplexVector n :=
    fun u => (realTangentCoords b (γ u)).comp ((realFrameCLM c (γ u)).comp (W u))
  have HEq : Z =ᶠ[𝓝 t] (fun u => (fderiv ℝ (realChartChange c b) (chartPt c (γ u))).comp (W u)) := by
    filter_upwards [hI.mem_nhds ht,hcont.preimage_mem_nhds
      ((chartAt (ComplexVector n) b).open_source.mem_nhds hb)] with u hu hbu
    have HM := realTangentCoords_comp_realFrameCLM_change c b (γ u) (hsource hu) hbu
    exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L.comp (W u)) HM
  have Hvalue : Z t = (fderiv ℝ (realChartChange c b) (chartPt c (γ t))).comp (W t) := HEq.self_of_nhds
  change HasDerivAt Z ((chartParallelCoefficient h b γ t).comp (Z t)) t
  rw [Hvalue]
  exact Hchange.congr_of_eventuallyEq HEq

end Yau.LeafProofs.L23Aux
