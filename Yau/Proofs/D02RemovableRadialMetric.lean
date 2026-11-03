import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Cauchy

open MeasureTheory Filter Set
open scoped Topology

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux

/-- A finite genuine speed integral makes the entire radial path Cauchy at
zero. Completeness yields a limit of the full path, not merely a subsequence. -/
theorem exists_radial_limit_of_integrable_speed
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {γ : ℝ → Y} {v : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hv : IntegrableOn v (Ioo 0 ρ) volume) (hv0 : ∀ s ∈ Ioo 0 ρ, 0 ≤ v s)
    (hdis : ∀ s ∈ Ioo 0 ρ, ∀ t ∈ Ioo 0 ρ, s ≤ t →
      dist (γ s) (γ t) ≤ ∫ r in Icc s t, v r) :
    ∃ p : Y, Tendsto γ (𝓝[>] 0) (𝓝 p) := by
  classical
  let V := (Ioo 0 ρ).indicator v
  have hV : Integrable V volume := (integrable_indicator_iff measurableSet_Ioo).mpr hv
  have hV0 : ∀ r, 0 ≤ V r := fun r ↦ indicator_nonneg (fun x hx ↦ hv0 x hx) r
  let G := fun t : ℝ ↦ ∫ r in (0 : ℝ)..t, V r
  have hG : Continuous G := hV.continuous_primitive 0
  have hG0 : G 0 = 0 := by simp [G]
  have hc : Cauchy (Filter.map γ (𝓝[>] (0 : ℝ))) := by
    rw [Metric.uniformity_basis_dist.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), G t < ε :=
      hG.continuousAt.tendsto.eventually_lt_const (by simpa only [hG0] using hε)
    obtain ⟨d, hd, hdG⟩ := Metric.mem_nhds_iff.mp hnear
    let δ := min (ρ / 2) (d / 2)
    have hδ : 0 < δ := lt_min (half_pos hρ) (half_pos hd)
    have hδρ : δ < ρ := (min_le_left _ _).trans_lt (half_lt_self hρ)
    have hδd : δ < d := (min_le_right _ _).trans_lt (half_lt_self hd)
    have hGδ : G δ < ε := hdG (by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ] using hδd)
    have hdist : ∀ s ∈ Ioo 0 δ, ∀ t ∈ Ioo 0 δ, s ≤ t → dist (γ s) (γ t) < ε := by
      intro s hs t ht hst
      have hsρ : s ∈ Ioo 0 ρ := ⟨hs.1, hs.2.trans hδρ⟩
      have htρ : t ∈ Ioo 0 ρ := ⟨ht.1, ht.2.trans hδρ⟩
      have heq : (∫ r in Icc s t, v r) = ∫ r in Icc s t, V r := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro r hr
        exact (indicator_of_mem (show r ∈ Ioo 0 ρ from ⟨hs.1.trans_le hr.1, hr.2.trans_lt htρ.2⟩) v).symm
      have hle : (∫ r in Icc s t, V r) ≤ G δ := by
        change (∫ r in Icc s t, V r) ≤ ∫ r in (0 : ℝ)..δ, V r
        rw [intervalIntegral.integral_of_le hδ.le]
        apply setIntegral_mono_set hV.integrableOn (Filter.Eventually.of_forall hV0)
        apply Filter.Eventually.of_forall
        intro r hr
        exact ⟨hs.1.trans_le hr.1, hr.2.trans ht.2.le⟩
      exact (hdis s hsρ t htρ hst).trans_lt (heq ▸ hle.trans_lt hGδ)
    refine ⟨γ '' Ioo 0 δ, Filter.image_mem_map (Ioo_mem_nhdsGT hδ), ?_⟩
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    rcases le_total s t with hst | hts
    · exact hdist s hs t ht hst
    · change dist (γ s) (γ t) < ε
      simpa only [dist_comm] using hdist t ht s hs hts
  exact cauchy_iff_exists_le_nhds.mp hc

end Yau.NodeProofs.D02RemovableAux
