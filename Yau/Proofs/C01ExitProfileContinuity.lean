import Yau.Proofs.C01ExitProfileMetricComparison

/-! The true minimum distance to each original sphere is continuous
for all nonnegative times. Uniform comparison is used only inside the
original compact ball, after restricting paths to their first exit. -/

noncomputable section

open Filter
open scoped Topology Manifold ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_exit_profile_continuousOn
    (hflow : LocalizedFlow X o h U P ρ) (L : ℝ) (hL : 0 < L) :
    ContinuousOn (fun t => exitDistanceProfile X.metric (h t) o L) (Set.Ici 0) := by
  intro a ha
  change Tendsto (fun t => exitDistanceProfile X.metric (h t) o L) (𝓝[Set.Ici 0] a)
    (𝓝 (exitDistanceProfile X.metric (h a) o L))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := exitDistanceProfile X.metric (h a) o L
  have hkₐ := localizedFlow_metricSmooth_nonneg hflow a ha
  have hA : 0 < A := exitDistanceProfile_pos X.metric (h a) hkₐ o L hL
  let δ := min (1 / 2 : ℝ) (ε / (A + 1))
  have hden : 0 < A + 1 := by linarith
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδprod : δ * A < ε := by
    have hscale : δ * (A + 1) ≤ ε := (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith
  have hK := isCompact_inducedDistance_sublevel X.metric o L
  filter_upwards [localizedFlow_compact_uniform_speedSq_comparison hflow _ hK a ha δ hδ hδ1,
    self_mem_nhdsWithin] with s hs hs₀
  have hkₛ := localizedFlow_metricSmooth_nonneg hflow s hs₀
  have hupper := exit_profile_upper_of_compact_metric_upper X.metric (h a) (h s) hkₐ hkₛ
    o L hL (1 + δ) (by linarith) (fun x hx v => (hs x hx v).2)
  have hlower := exit_profile_lower_of_compact_metric_lower X.metric (h a) (h s) hkₐ hkₛ
    o L hL (1 - δ) (by linarith) (fun x hx v => (hs x hx v).1)
  rw [Real.dist_eq]
  apply lt_of_le_of_lt (b := δ * A) _ hδprod
  apply abs_le.mpr
  dsimp only [A] at hlower hupper ⊢
  constructor <;> nlinarith

end Yau.NodeProofs.C01Aux
