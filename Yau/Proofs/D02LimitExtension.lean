import Yau.Proofs.D02ChartCompactness

/-! A continuous regular-domain limit is made into a total function
without changing any interior witness or convergence statement. -/

open scoped Topology
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux

def domainLimitExtension {Y : Type*} [TopologicalSpace Y] [Nonempty Y]
    {O : Set ℂ} (f : C(O, Y)) (z : ℂ) : Y := by
  classical
  exact if hz : z ∈ O then f ⟨z, hz⟩ else Classical.choice inferInstance

theorem domainLimitExtension_of_mem {Y : Type*} [TopologicalSpace Y] [Nonempty Y]
    {O : Set ℂ} (f : C(O, Y)) {z : ℂ} (hz : z ∈ O) :
    domainLimitExtension f z = f ⟨z, hz⟩ := by simp [domainLimitExtension, hz]

theorem domainLimitExtension_continuousOn {Y : Type*} [TopologicalSpace Y] [Nonempty Y]
    {O : Set ℂ} (f : C(O, Y)) : ContinuousOn (domainLimitExtension f) O := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  funext z
  exact domainLimitExtension_of_mem f z.2

theorem domainLimitExtension_tendstoLocallyUniformly {Y : Type*} [MetricSpace Y] [Nonempty Y]
    {O : Set ℂ} (hO : IsOpen O) (fs : ℕ → ℂ → Y) (f : C(O, Y))
    (hconv : ∀ L : Set O, IsCompact L →
      TendstoUniformlyOn (fun j (z : O) => fs j z) f atTop L) :
    TendstoLocallyUniformlyOn fs (domainLimitExtension f) atTop O := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hO]
  intro K hKO hK
  let K' : Set O := (Subtype.val : O → ℂ) ⁻¹' K
  have hK' : IsCompact K' := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    hK (by simpa only [Subtype.range_coe] using hKO)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv K' hK')) ε hε] with j hj z hz
  simpa only [domainLimitExtension_of_mem f (hKO hz)] using hj ⟨z, hKO hz⟩ hz

end Yau.NodeProofs.D02Aux
