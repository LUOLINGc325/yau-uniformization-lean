import Yau.LeafProofs.L23FieldMetricGeodesicShift

/-! Matching actual phases glue genuine geodesics on overlapping open intervals. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem geoChartState_congr_eventuallyEq (f g : ℝ → M.Carrier) (c : M.Carrier) (t : ℝ)
    (heq : f =ᶠ[𝓝 t] g) : geoChartState f c t = geoChartState g c t := by
  have Hcoord : (fun u => chartPt c (f u)) =ᶠ[𝓝 t] (fun u => chartPt c (g u)) :=
    heq.fun_comp (chartPt c)
  apply Prod.ext
  · exact Hcoord.self_of_nhds
  · exact Hcoord.deriv_eq

theorem fieldGeodesicOn_of_locally_eq (h : HermitianField M) (Γ : ℝ → M.Carrier)
    (J : Set ℝ)
    (hlocal : ∀ u ∈ J, ∃ (γ : ℝ → M.Carrier) (U : Set ℝ),
      IsOpen U ∧ u ∈ U ∧ FieldGeodesicOn h γ U ∧ Γ =ᶠ[𝓝 u] γ) :
    FieldGeodesicOn h Γ J := by
  letI := manifold_realSmooth M
  refine ⟨?_,?_⟩
  · intro u hu
    obtain ⟨γ,U,hU,huU,hγ,heq⟩ := hlocal u hu
    exact ((hγ.1 u huU).contMDiffAt (hU.mem_nhds huU)).congr_of_eventuallyEq heq |>.contMDiffWithinAt
  · intro c u hu hc
    obtain ⟨γ,U,hU,huU,hγ,heq⟩ := hlocal u hu
    have hsrc : γ u ∈ (extChartAt (ComplexModel n) c).source := by
      rw [← heq.self_of_nhds]
      exact hc
    have H := hγ.2 c u huU hsrc
    have hstate : geoChartState Γ c =ᶠ[𝓝 u] geoChartState γ c :=
      heq.eventuallyEq_nhds.mono (fun t ht => geoChartState_congr_eventuallyEq Γ γ c t ht)
    have hstate₀ : geoChartState Γ c u = geoChartState γ c u := hstate.self_of_nhds
    rw [← hstate₀] at H
    exact H.congr_of_eventuallyEq hstate

theorem fieldGeodesicOn_splice
    (h : HermitianField M) (hh : MetricSmooth h) (f g : ℝ → M.Carrier)
    (a b c d T : ℝ)
    (hf : FieldGeodesicOn h f (Set.Ioo a b)) (hg : FieldGeodesicOn h g (Set.Ioo c d))
    (hfT : T ∈ Set.Ioo a b) (hgT : T ∈ Set.Ioo c d) (z : M.Carrier)
    (hsf : f T ∈ (extChartAt (ComplexModel n) z).source)
    (hsg : g T ∈ (extChartAt (ComplexModel n) z).source)
    (hphase : geoChartState f z T = geoChartState g z T) :
    FieldGeodesicOn h (fun u => if u ≤ T then f u else g u) (Set.Ioo a d) := by
  have heq := fieldGeodesics_eventuallyEq_of_same_chart_phase h hh z f g isOpen_Ioo isOpen_Ioo
    hf hg T hfT hgT hsf hsg hphase
  apply fieldGeodesicOn_of_locally_eq
  intro u hu
  by_cases huT : u < T
  · refine ⟨f,Set.Ioo a b,isOpen_Ioo,⟨hu.1,huT.trans hfT.2⟩,hf,?_⟩
    filter_upwards [Iio_mem_nhds huT] with s hs
    exact if_pos hs.le
  · by_cases hTu : T < u
    · refine ⟨g,Set.Ioo c d,isOpen_Ioo,⟨hgT.1.trans hTu,hu.2⟩,hg,?_⟩
      filter_upwards [Ioi_mem_nhds hTu] with s hs
      exact if_neg (not_le.mpr hs)
    · have huEq : u = T := le_antisymm (le_of_not_gt hTu) (le_of_not_gt huT)
      subst u
      exact ⟨f,Set.Ioo a b,isOpen_Ioo,hfT,hf,splice_eventuallyEq_left f g T heq⟩

end Yau.LeafProofs.L23Aux
