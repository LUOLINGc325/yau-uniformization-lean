import Yau.Proofs.F01GlobalChartSmoothLimit

/-! Smoothness on every genuine closed finite time slab gives smoothness
on the original closed nonnegative-time domain, including its initial face. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_nonnegative_time_of_closed_slabs
    {S : Set E} {f : E × ℝ → F}
    (hf : ∀ k : ℕ, ContDiffOn ℝ ∞ f (S ×ˢ Icc 0 ((k : ℝ) + 1))) :
    ContDiffOn ℝ ∞ f (S ×ˢ Ici 0) := by
  intro p hp
  obtain ⟨k, hk⟩ := exists_nat_gt p.2
  have ht : p.2 < (k : ℝ) + 1 := by linarith
  apply (hf k p ⟨hp.1, hp.2, ht.le⟩).mono_of_mem_nhdsWithin
  have hN : {q : E × ℝ | q.2 < (k : ℝ) + 1} ∈ 𝓝 p :=
    (isOpen_Iio.preimage continuous_snd).mem_nhds ht
  filter_upwards [mem_nhdsWithin_of_mem_nhds hN, self_mem_nhdsWithin] with q hq hqS
  exact ⟨hqS.1, hqS.2, hq.le⟩

end Yau.NodeProofs.F01Aux
