import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

open scoped Topology
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02FiberLimitAux

/-- Uniform convergence on a compact parameter set puts all late values in
one genuine compact subset of any prescribed open target neighborhood. -/
theorem uniform_limit_eventually_compact {D Y : Type*}
    [TopologicalSpace D] [MetricSpace Y] [ProperSpace Y]
    {fs : ℕ → D → Y} {f : D → Y} {K : Set D} (hK : IsCompact K)
    (hc : ContinuousOn f K) (hconv : TendstoUniformlyOn fs f atTop K)
    {V : Set Y} (hV : IsOpen V) (hfV : MapsTo f K V) :
    ∃ Q : Set Y, IsCompact Q ∧ Q ⊆ V ∧ MapsTo f K Q ∧
      ∀ᶠ j in atTop, MapsTo (fs j) K Q := by
  have himage : IsCompact (f '' K) := hK.image_of_continuousOn hc
  obtain ⟨δ, hδ, hδV⟩ := himage.exists_cthickening_subset_open hV (image_subset_iff.mpr hfV)
  refine ⟨cthickening δ (f '' K), himage.cthickening, hδV,
    fun z hz ↦ self_subset_cthickening _ (mem_image_of_mem f hz), ?_⟩
  have hlate := (Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ
  filter_upwards [hlate] with j hj z hz
  exact mem_cthickening_of_dist_le (fs j z) (f z) δ (f '' K) (mem_image_of_mem f hz)
    (by simpa only [dist_comm] using (hj z hz).le)

/-- Continuous reconstruction on one valid open target set preserves uniform
convergence; compactness supplies the required uniform continuity internally. -/
theorem uniform_limit_compact_composition {D Y Z : Type*}
    [TopologicalSpace D] [MetricSpace Y] [ProperSpace Y] [UniformSpace Z]
    {fs : ℕ → D → Y} {f : D → Y} {K : Set D} (hK : IsCompact K)
    (hc : ContinuousOn f K) (hconv : TendstoUniformlyOn fs f atTop K)
    {V : Set Y} (hV : IsOpen V) (hfV : MapsTo f K V)
    (c : Y → Z) (hcoord : ContinuousOn c V) :
    (∀ᶠ j in atTop, MapsTo (fs j) K V) ∧
      TendstoUniformlyOn (fun j z ↦ c (fs j z)) (fun z ↦ c (f z)) atTop K := by
  obtain ⟨Q, hQ, hQV, hfQ, hfsQ⟩ := uniform_limit_eventually_compact hK hc hconv hV hfV
  refine ⟨hfsQ.mono (fun j hj z hz ↦ hQV (hj hz)), ?_⟩
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hfsQ hfQ
    (hQ.uniformContinuousOn_of_continuous (hcoord.mono hQV)) hconv

theorem uniform_pair {D Y Z : Type*} [MetricSpace Y] [MetricSpace Z]
    {fs : ℕ → D → Y} {f : D → Y} {es : ℕ → D → Z} {e : D → Z} {K : Set D}
    (hf : TendstoUniformlyOn fs f atTop K) (he : TendstoUniformlyOn es e atTop K) :
    TendstoUniformlyOn (fun j z ↦ (fs j z, es j z)) (fun z ↦ (f z, e z)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at hf he ⊢
  intro ε hε
  filter_upwards [hf ε hε, he ε hε] with j hjf hje z hz
  exact max_lt (hjf z hz) (hje z hz)

end Yau.NodeProofs.D02FiberLimitAux
