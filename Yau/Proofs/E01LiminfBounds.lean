import Mathlib.Topology.Instances.EReal.Lemmas

/-! Continuous lower bounds and exact positive scaling survive the original neighborhood liminf. -/

noncomputable section
open scoped Topology
open Filter Set

namespace Yau.NodeProofs.E01Aux

theorem continuous_real_lower_bound_liminf
    {P : Type*} [TopologicalSpace P] (f : P → EReal) (g : P → ℝ)
    (S : Set P) {p : P} (hp : p ∈ S) (hg : ContinuousAt g p)
    (hle : ∀ q ∈ S, (g q : EReal) ≤ f q) :
    (g p : EReal) ≤ liminf f (𝓝[S] p) := by
  haveI : NeBot (𝓝[S] p) := nhdsWithin_neBot_of_mem hp
  have ht : Tendsto (fun q => (g q : EReal)) (𝓝[S] p) (𝓝 (g p : EReal)) :=
    (continuous_coe_real_ereal.continuousAt.tendsto.comp hg.tendsto).mono_left nhdsWithin_le_nhds
  rw [← ht.liminf_eq]
  have hs : ∀ᶠ q in 𝓝[S] p, q ∈ S := self_mem_nhdsWithin
  exact liminf_le_liminf (hs.mono (fun q hq => hle q hq))

theorem liminf_scaling_of_filter_map
    {P : Type*} (f : P → EReal) (e : P → P) (l l' : Filter P) [NeBot l]
    (hmap : Filter.map e l = l') (c : ℝ) (hc : 0 ≤ c)
    (hscale : ∀ q, f (e q) = (c : EReal) * f q) :
    liminf f l' = (c : EReal) * liminf f l := by
  rw [← hmap, ← liminf_comp]
  simp only [Function.comp_def, hscale]
  exact EReal.liminf_const_mul_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c)

end Yau.NodeProofs.E01Aux
