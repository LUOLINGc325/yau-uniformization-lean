import Yau.Proofs.F04FiniteMass

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.F04Proof


/-- Uniform integrability is monotone under norm domination even for
functions taking values in different normed spaces. -/
theorem unifIntegrable_mono_norm
    {X E F ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure X} {p : ℝ≥0∞} {U : ι → X → E} {W : ι → X → F}
    (hU : UnifIntegrable U p μ) (hW : ∀ j, AEStronglyMeasurable (W j) μ)
    (hbound : ∀ j x, ‖W j x‖ ≤ ‖U j x‖) : UnifIntegrable W p μ := by
  apply unifIntegrable_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hdom⟩ := unifIntegrable_iff.mp hU ε hε
  refine ⟨δ, hδ, ?_⟩
  intro j s hs
  have hm : eLpNorm (W j) p (μ.restrict s) ≤ eLpNorm (U j) p (μ.restrict s) :=
    eLpNorm_mono_enorm_ae (hW j).restrict
      (ae_of_all _ fun x => enorm_le_iff_norm_le.mpr (hbound j x))
  exact hm.trans (hdom j s hs)

/-- On the finite physical time measure, a continuous norm-decreasing map
preserves strong L2 convergence. Uniform integrability and AE subsequences
justify the limit without imposing a false domination on the full sequence. -/
theorem continuous_normContractive_comp_L2
    {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure X) [IsFiniteMeasure μ]
    (Θ : E → F) (hΘ : Continuous Θ) (hbound : ∀ v, ‖Θ v‖ ≤ ‖v‖)
    (U : ℕ → X → E) (u : X → E) (hU : ∀ j, MemLp (U j) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun j => eLpNorm (U j - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x => Θ (U j x) - Θ (u x)) 2 μ) atTop (𝓝 0) := by
  have hOne : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hui : UnifIntegrable U 2 μ :=
    unifIntegrable_of_tendsto_Lp (p := (2 : ℝ≥0∞)) (f := U) (g := u) hOne hp' hU hu hlim
  have hm (j : ℕ) : AEStronglyMeasurable (fun x => Θ (U j x)) μ :=
    hΘ.comp_aestronglyMeasurable (hU j).aestronglyMeasurable
  have hmu : MemLp (fun x => Θ (u x)) 2 μ :=
    hu.of_le (hΘ.comp_aestronglyMeasurable hu.aestronglyMeasurable)
      (ae_of_all μ fun x => hbound (u x))
  have hΘui : UnifIntegrable (fun j x => Θ (U j x)) 2 μ :=
    unifIntegrable_mono_norm hui hm (fun j x => hbound (U j x))
  have hmeasure : TendstoInMeasure μ U atTop u := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hlim
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hsubmeasure : TendstoInMeasure μ (fun j => U (ns j)) atTop u :=
    fun ε hε => (hmeasure ε hε).comp hns
  obtain ⟨ms, _, hms⟩ := hsubmeasure.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hp : ∀ᵐ x ∂μ, Tendsto (fun j => Θ (U (ns (ms j)) x)) atTop (𝓝 (Θ (u x))) := by
    filter_upwards [hms] with x hx
    exact hΘ.continuousAt.tendsto.comp hx
  have ht := tendsto_Lp_finite_of_tendsto_ae (p := (2 : ℝ≥0∞)) hOne hp'  (fun j => hm (ns (ms j))) hmu
    (hΘui.comp (fun j => ns (ms j))) hp
  simpa only [Function.comp_def, Pi.sub_def] using ht

end Yau.F04Proof
