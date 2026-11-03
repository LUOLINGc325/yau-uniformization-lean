import Yau.Proofs.V03C1Dirichlet

/-! Uniform trace convergence gives convergence of the original normalized
circle average. Domination is derived from the limiting continuous trace. -/

open scoped Topology
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleAverage_tendsto_of_uniform {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (U : α → ℝ → ℝ) (u : ℝ → ℝ) (hU : ∀ᶠ a in l, Continuous (U a)) (hu : Continuous u)
    (hunif : TendstoUniformlyOn U u l (Set.Icc 0 (2 * Real.pi))) :
    Tendsto (fun a => circleAverage (U a)) l (𝓝 (circleAverage u)) := by
  have hnonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hbound := (Metric.tendstoUniformlyOn_iff.mp hunif) 1 zero_lt_one
  have hmeas : ∀ᶠ a in l, AEStronglyMeasurable (U a)
      (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := hU.mono fun a ha => ha.aestronglyMeasurable
  have hdom : ∀ᶠ a in l, ∀ᵐ θ ∂volume, θ ∈ Set.uIoc 0 (2 * Real.pi) →
      ‖U a θ‖ ≤ ‖u θ‖ + 1 := by
    filter_upwards [hbound] with a ha
    apply Eventually.of_forall
    intro θ hθ
    have hi : θ ∈ Set.Icc 0 (2 * Real.pi) := by
      simpa only [Set.uIcc_of_le hnonneg] using Set.uIoc_subset_uIcc hθ
    have hd := ha θ hi
    rw [dist_eq_norm, norm_sub_rev] at hd
    have hn := norm_add_le (U a θ - u θ) (u θ)
    rw [sub_add_cancel] at hn
    linarith
  have hlim : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc 0 (2 * Real.pi) →
      Tendsto (fun a => U a θ) l (𝓝 (u θ)) := by
    apply Eventually.of_forall
    intro θ hθ
    apply hunif.tendsto_at
    simpa only [Set.uIcc_of_le hnonneg] using Set.uIoc_subset_uIcc hθ
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ => ‖u θ‖ + 1) hmeas hdom
    ((hu.norm.add continuous_const).intervalIntegrable _ _) hlim
  exact ht.const_mul (2 * Real.pi)⁻¹

end Yau.Blueprint.V03Proof
