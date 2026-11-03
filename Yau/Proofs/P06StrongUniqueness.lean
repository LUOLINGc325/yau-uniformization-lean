import Yau.Proofs.P06HodgeSpectral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem strongPositiveHeat_zero (T : H →ₗ.[ℝ] H)
    (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u)) (h : ℝ → H)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧ (h t, (-2 : ℝ) • w) ∈ T.graph)
    (hinit : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 0)) : ∀ t, 0 < t → h t = 0 := by
  let F : ℝ → ℝ := fun t => ‖h t‖ ^ 2
  have hderiv (t : ℝ) (ht : 0 < t) :
      DifferentiableAt ℝ F t ∧ deriv F t ≤ 0 := by
    obtain ⟨w, hd, hg⟩ := hheat t ht
    obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp hg
    change (u : H) = h t at hu
    change T u = (-2 : ℝ) • w at hTu
    have hpos := hp u
    rw [hTu, hu, inner_smul_right] at hpos
    refine ⟨hd.norm_sq.differentiableAt, ?_⟩
    rw [show deriv F t = 2 * inner ℝ (h t) w from hd.norm_sq.deriv]
    linarith
  have hanti : AntitoneOn F (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro t ht
      exact (hderiv t ht).1.continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      intro t ht
      exact (hderiv t ht).1.differentiableWithinAt
    · rw [interior_Ioi]
      intro t ht
      exact (hderiv t ht).2
  have hFinit : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [F, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hinit.norm.pow 2
  intro t ht
  have hFt : F t ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hFinit
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hs hst
    exact hanti hs ht hst.le
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hFt (sq_nonneg _)))

theorem strongPositiveHeat_unique (T : H →ₗ.[ℝ] H)
    (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u)) (h v : ℝ → H) (f : H)
    (hh : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧ (h t, (-2 : ℝ) • w) ∈ T.graph)
    (hv : ∀ t, 0 < t → ∃ w, HasDerivAt v w t ∧ (v t, (-2 : ℝ) • w) ∈ T.graph)
    (hhinit : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 f))
    (hvinit : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 f)) :
    ∀ t, 0 < t → h t = v t := by
  have hz := strongPositiveHeat_zero T hp (fun t => h t - v t) (fun t ht => by
    obtain ⟨w, hd, hg⟩ := hh t ht
    obtain ⟨z, vd, vg⟩ := hv t ht
    refine ⟨w - z, hd.sub vd, ?_⟩
    have hout := T.graph.sub_mem hg vg
    change (h t - v t, (-2 : ℝ) • w - (-2 : ℝ) • z) ∈ T.graph at hout
    simpa only [smul_sub] using hout)
    (by simpa only [sub_self] using hhinit.sub hvinit)
  exact fun t ht => sub_eq_zero.mp (hz t ht)

end Hilbert

open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Uniqueness in the actual Hilbert strong-path class identifies every
such path with the constructed spectral heat. -/
theorem hodgeStrongPath_eq_heat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t, (-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (hinit : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 f)) :
    ∀ t, 0 < t → h t = hodgeHeatHilbert g μ hμ k t f :=
  strongPositiveHeat_unique (hodgeCompleteOperator g μ hμ k)
    (hodgeCompleteOperator_nonnegative g μ hμ k) h (fun t => hodgeHeatHilbert g μ hμ k t f) f
    hheat (hodgeHeatHilbert_strongPath g μ hμ k f) hinit
    ((hodgeHeatHilbert_tendsto_zero g μ hμ k f).mono_left
      (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self))

end Yau.NodeProofs.P06Aux
