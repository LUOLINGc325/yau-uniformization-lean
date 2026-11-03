import Yau.Proofs.P02BisectionalBound
import Yau.Proofs.P02EnergyPair

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

theorem fieldGeodesic_velocity_coords (h : HermitianField M)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (c : M.Carrier) (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ))
    (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :
    realTangentCoords c (γ u) (realCurveVelocity γ u) = (geoChartState γ c u).2 := by
  letI := manifold_realSmooth M
  have hc' : γ u ∈ (extChartAt (ComplexModel n) c).source := by
    simpa only [extChartAt_source] using hc
  have HA := (hγ.1 u hu).contMDiffAt (isOpen_Ioo.mem_nhds hu)
  exact realCurveVelocity_coords_of_hasDerivAt γ u c _ hc
    (HA.mdifferentiableAt (by norm_num)) (hγ.2 c u hu hc').fst

theorem parallelBisectional_eq_transport (h : HermitianField M) (hs : MetricSmooth h)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (w : ComplexVector n) (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ)) :
    parallelBisectional h γ P w u =
      transportBisectional h ⟨γ u,(realCurveVelocity γ u,P u w)⟩ := by
  rw [transportBisectional_in_chart h hs (γ u) _ (mem_chart_source _ _),
    fieldGeodesic_velocity_coords h γ δ hγ (γ u) u hu (mem_chart_source _ _)]
  rfl

theorem parallelBisectional_in_chart (h : HermitianField M) (hs : MetricSmooth h)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (c : M.Carrier) (w : ComplexVector n) (u : ℝ)
    (hu : u ∈ Set.Ioo (-δ) (1+δ))
    (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :
    parallelBisectional h γ P w u =
      coordinateBisectional h c (chartPt c (γ u)) (geoChartState γ c u).2
        (realTangentCoords c (γ u) (P u w)) := by
  rw [parallelBisectional_eq_transport h hs γ δ hγ P w u hu,
    transportBisectional_in_chart h hs c _ hc,
    fieldGeodesic_velocity_coords h γ δ hγ c u hu hc]

theorem parallelBisectional_continuousOn (h : HermitianField M) (hs : MetricSmooth h)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier)
    (H : ParallelVariationData h γ δ e P A)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ))) (w : ComplexVector n) :
    ContinuousOn (parallelBisectional h γ P w) (Set.Ioo (-δ) (1+δ)) := by
  letI := manifold_realSmooth M
  intro u hu
  let c := γ u
  have hc : γ u ∈ (extChartAt (ComplexModel n) c).source := mem_extChartAt_source c
  have HC := (hγ.2 c u hu hc).continuousAt
  have HV := ((H.jets c u hu hc).1 w).continuousAt
  have Hz : chartPt c (γ u) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source hc
  have HB := coordinateBisectional_continuousAt_comp h hs c
    (fun t => chartPt c (γ t)) (fun t => (geoChartState γ c t).2)
    (fun t => realTangentCoords c (γ t) (P t w)) u HC.fst HC.snd HV Hz
  have hsrc : ∀ᶠ t in 𝓝 u, γ t ∈ (chartAt (ComplexVector n) c).source :=
    (hγ.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hu)).preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _))
  apply ContinuousAt.continuousWithinAt
  apply HB.congr_of_eventuallyEq
  filter_upwards [hsrc,isOpen_Ioo.mem_nhds hu] with t ht hti
  exact parallelBisectional_in_chart h hs γ δ hγ P c w t hti ht

theorem parallelBisectional_nonneg (h : HermitianField M) (hs : MetricSmooth h)
    (hp : PaperPositiveBisectional h) (γ : ℝ → M.Carrier) (δ : ℝ)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (w : ComplexVector n) (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ)) :
    0 ≤ parallelBisectional h γ P w u := by
  rw [parallelBisectional_eq_transport h hs γ δ hγ P w u hu]
  exact transportBisectional_nonneg h hp _ _ _

end Yau.NodeProofs.P02Aux
