import Yau.LeafProofs.L23FieldMetricNormalPhase

/-! Actual local spray uniqueness gives genuine smooth gluing at a matching phase. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold NNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem chartGeodesics_eventuallyEq_of_same_phase
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (f g : ℝ → ComplexVector n × ComplexVector n) (t : ℝ)
    (hf : ∀ᶠ u in 𝓝 t, (f u).1 ∈ chartTarget c ∧
      HasDerivAt f (chartGeodesicSpray h c (f u)) u)
    (hg : ∀ᶠ u in 𝓝 t, (g u).1 ∈ chartTarget c ∧
      HasDerivAt g (chartGeodesicSpray h c (g u)) u)
    (heq : f t = g t) : f =ᶠ[𝓝 t] g := by
  have htarget : f t ∈ chartTarget c ×ˢ (Set.univ : Set (ComplexVector n)) :=
    ⟨hf.self_of_nhds.1,Set.mem_univ _⟩
  have hF : ContDiffAt ℝ ∞ (chartGeodesicSpray h c) (f t) :=
    (chartGeodesicSpray_contDiffOn h hh c).contDiffAt
      (((isOpen_extChartAt_target (I := ComplexModel n) c).prod isOpen_univ).mem_nhds htarget)
  obtain ⟨K,U,hU,hLip⟩ := (hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
  have hfc : ContinuousAt f t := hf.self_of_nhds.2.continuousAt
  have hgc : ContinuousAt g t := hg.self_of_nhds.2.continuousAt
  have hUg : U ∈ 𝓝 (g t) := by rw [← heq]; exact hU
  apply ODE_solution_unique_of_eventually (v := fun _ => chartGeodesicSpray h c)
    (s := fun _ => U) (K := K) (Eventually.of_forall fun _ => hLip) ?_ ?_ heq
  · filter_upwards [hf,hfc.preimage_mem_nhds hU] with u hu hmu
    exact ⟨hu.2,hmu⟩
  · filter_upwards [hg,hgc.preimage_mem_nhds hUg] with u hu hmu
    exact ⟨hu.2,hmu⟩

theorem fieldGeodesics_eventuallyEq_of_same_chart_phase
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (γ₁ γ₂ : ℝ → M.Carrier) {J₁ J₂ : Set ℝ} (hJ₁ : IsOpen J₁) (hJ₂ : IsOpen J₂)
    (hγ₁ : FieldGeodesicOn h γ₁ J₁) (hγ₂ : FieldGeodesicOn h γ₂ J₂)
    (t : ℝ) (ht₁ : t ∈ J₁) (ht₂ : t ∈ J₂)
    (hc₁ : γ₁ t ∈ (extChartAt (ComplexModel n) c).source)
    (hc₂ : γ₂ t ∈ (extChartAt (ComplexModel n) c).source)
    (heq : geoChartState γ₁ c t = geoChartState γ₂ c t) : γ₁ =ᶠ[𝓝 t] γ₂ := by
  letI := manifold_realSmooth M
  have hcont₁ : ContinuousAt γ₁ t := hγ₁.1.continuousOn.continuousAt (hJ₁.mem_nhds ht₁)
  have hcont₂ : ContinuousAt γ₂ t := hγ₂.1.continuousOn.continuousAt (hJ₂.mem_nhds ht₂)
  have hs₁ : ∀ᶠ u in 𝓝 t, γ₁ u ∈ (extChartAt (ComplexModel n) c).source :=
    hcont₁.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) c).mem_nhds hc₁)
  have hs₂ : ∀ᶠ u in 𝓝 t, γ₂ u ∈ (extChartAt (ComplexModel n) c).source :=
    hcont₂.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) c).mem_nhds hc₂)
  have hsol₁ : ∀ᶠ u in 𝓝 t, (geoChartState γ₁ c u).1 ∈ chartTarget c ∧
      HasDerivAt (geoChartState γ₁ c) (chartGeodesicSpray h c (geoChartState γ₁ c u)) u := by
    filter_upwards [hJ₁.mem_nhds ht₁,hs₁] with u hu hcu
    exact ⟨(extChartAt (ComplexModel n) c).map_source hcu,hγ₁.2 c u hu hcu⟩
  have hsol₂ : ∀ᶠ u in 𝓝 t, (geoChartState γ₂ c u).1 ∈ chartTarget c ∧
      HasDerivAt (geoChartState γ₂ c) (chartGeodesicSpray h c (geoChartState γ₂ c u)) u := by
    filter_upwards [hJ₂.mem_nhds ht₂,hs₂] with u hu hcu
    exact ⟨(extChartAt (ComplexModel n) c).map_source hcu,hγ₂.2 c u hu hcu⟩
  have H := chartGeodesics_eventuallyEq_of_same_phase h hh c _ _ t hsol₁ hsol₂ heq
  filter_upwards [H,hs₁,hs₂] with u hu hcu₁ hcu₂
  apply (extChartAt (ComplexModel n) c).injOn hcu₁ hcu₂
  exact congrArg Prod.fst hu

theorem splice_eventuallyEq_left {α : Type*} (f g : ℝ → α) (t : ℝ)
    (heq : f =ᶠ[𝓝 t] g) : (fun u => if u ≤ t then f u else g u) =ᶠ[𝓝 t] f := by
  filter_upwards [heq] with u hu
  split_ifs <;> simp_all

end Yau.LeafProofs.L23Aux
