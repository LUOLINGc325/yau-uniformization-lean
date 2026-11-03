import Yau.LeafProofs.L23LocalDistanceSupportContracts

/-! A genuine coordinate spray solution satisfies the geodesic equation in
every overlapping chart, under MetricSmooth alone. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

theorem geoChartState_chart_solution_eq (h : HermitianField M)
    (c b : M.Carrier) (η : ℝ → ComplexVector n × ComplexVector n) (u : ℝ)
    (hz : (η u).1 ∈ chartTarget c)
    (hb : chartInv c (η u).1 ∈ (extChartAt (ComplexModel n) b).source)
    (hη : HasDerivAt η (chartGeodesicSpray h c (η u)) u) :
    geoChartState (fun s => chartInv c (η s).1) b u = realTangentChartChange c b (η u) := by
  have hpos : HasDerivAt (fun s => (η s).1) (η u).2 u := by
    convert! (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt u hη using 1 <;>
      simp only [chartGeodesicSpray]
  have H := ((realChartChange_contDiffAt c b hz hb).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt u hpos
  apply Prod.ext
  · rfl
  · change deriv (fun s => realChartChange c b (η s).1) u =
      fderiv ℝ (realChartChange c b) (η u).1 (η u).2
    exact H.deriv

theorem fieldGeodesicOn_of_chart_solution
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (η : ℝ → ComplexVector n × ComplexVector n) {J : Set ℝ}
    (hJ : IsOpen J) (hηC3 : ContDiffOn ℝ 3 η J)
    (hη : ∀ u ∈ J, (η u).1 ∈ chartTarget c ∧
      HasDerivAt η (chartGeodesicSpray h c (η u)) u) :
    FieldGeodesicOn h (fun u => chartInv c (η u).1) J := by
  letI := manifold_realSmooth M
  have hfst := contDiff_fst.comp_contDiffOn hηC3
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun u => chartInv c (η u).1) J :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) (n := 3) c).comp
      hfst.contMDiffOn (fun u hu => (hη u hu).1)
  refine ⟨hγ,?_⟩
  intro b u hu hb
  have hγc : ContinuousAt (fun s => chartInv c (η s).1) u :=
    hγ.continuousOn.continuousAt (hJ.mem_nhds hu)
  have hState : geoChartState (fun s => chartInv c (η s).1) b =ᶠ[𝓝 u]
      (fun s => realTangentChartChange c b (η s)) := by
    filter_upwards [hJ.mem_nhds hu,
      hγc.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) b).mem_nhds hb)] with s hs hsB
    exact geoChartState_chart_solution_eq h c b η s (hη s hs).1 hsB (hη s hs).2
  have H := ((realTangentChartChange_contDiffAt c b (η u) (hη u hu).1 hb).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt u (hη u hu).2
  rw [realTangentChartChange_fderiv_spray h hh c b (η u) (hη u hu).1 hb] at H
  have hval : geoChartState (fun s => chartInv c (η s).1) b u =
      realTangentChartChange c b (η u) := hState.self_of_nhds
  rw [← hval] at H
  exact H.congr_of_eventuallyEq hState

end Yau.LeafProofs.L23Aux
