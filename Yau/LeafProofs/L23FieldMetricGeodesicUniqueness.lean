import Yau.LeafProofs.L23FieldMetricGeodesicSplice

/-! Local actual spray uniqueness propagates along the full connected time interval. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem fieldGeodesics_eqOn_Ioo_of_same_chart_phase
    (h : HermitianField M) (hh : MetricSmooth h) (γ β : ℝ → M.Carrier)
    {a b t₀ : ℝ} (hγ : FieldGeodesicOn h γ (Set.Ioo a b))
    (hβ : FieldGeodesicOn h β (Set.Ioo a b)) (ht₀ : t₀ ∈ Set.Ioo a b)
    (c : M.Carrier) (hcγ : γ t₀ ∈ (extChartAt (ComplexModel n) c).source)
    (hcβ : β t₀ ∈ (extChartAt (ComplexModel n) c).source)
    (heq : geoChartState γ c t₀ = geoChartState β c t₀) :
    Set.EqOn γ β (Set.Ioo a b) := by
  letI := manifold_realSmooth M
  let S := Set.Ioo a b
  letI : PreconnectedSpace S := Subtype.preconnectedSpace (convex_Ioo a b).isPreconnected
  let V : Set S := {t | γ =ᶠ[𝓝 t.val] β}
  have hclosed : IsClosed V := by
    apply isClosed_iff_frequently.mpr
    intro t ht
    have hpos : γ t.val = β t.val := tendsto_nhds_unique_of_frequently_eq
      ((hγ.1.continuousOn.restrict).continuousAt)
      ((hβ.1.continuousOn.restrict).continuousAt)
      (ht.mono (fun s hs => hs.self_of_nhds))
    let d := γ t.val
    have hdγ : γ t.val ∈ (extChartAt (ComplexModel n) d).source := mem_extChartAt_source _
    have hdβ : β t.val ∈ (extChartAt (ComplexModel n) d).source := by rw [← hpos]; exact hdγ
    have Hγ : ContinuousAt (geoChartState γ d) t.val := (hγ.2 d t.val t.property hdγ).continuousAt
    have Hβ : ContinuousAt (geoChartState β d) t.val := (hβ.2 d t.val t.property hdβ).continuousAt
    have Hphase : geoChartState γ d t.val = geoChartState β d t.val :=
      tendsto_nhds_unique_of_frequently_eq
        (Hγ.comp continuousAt_subtype_val) (Hβ.comp continuousAt_subtype_val)
        (ht.mono (fun s hs => geoChartState_congr_eventuallyEq γ β d s.val hs))
    exact fieldGeodesics_eventuallyEq_of_same_chart_phase h hh d γ β isOpen_Ioo isOpen_Ioo
      hγ hβ t.val t.property t.property hdγ hdβ Hphase
  have hopen : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact continuousAt_subtype_val.eventually (eventually_eventually_nhds.mpr ht)
  have hV : V = Set.univ := IsClopen.eq_univ ⟨hclosed,hopen⟩
    ⟨⟨t₀,ht₀⟩,fieldGeodesics_eventuallyEq_of_same_chart_phase h hh c γ β isOpen_Ioo isOpen_Ioo
      hγ hβ t₀ ht₀ ht₀ hcγ hcβ heq⟩
  intro t ht
  have H : (⟨t,ht⟩ : S) ∈ V := by rw [hV]; exact Set.mem_univ _
  exact H.self_of_nhds

end Yau.LeafProofs.L23Aux
