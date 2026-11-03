import Yau.Proofs.F04ZeroPastLp

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic

/-- Genuine positive-time smoothness and actual local one-sided initial
 charts give smoothness on EVERY smaller full closed slab. The upper
 endpoint is handled inside the original larger time horizon. -/
theorem contDiffOn_closedSlab_of_local_initial
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {S T : ℝ} (hTS : T < S)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (hInitial : ∀ V : Set (Space n), IsOpen V → IsCompact (closure V) → closure V ⊆ O →
      ∃ s : ℝ, 0 < s ∧ s < S ∧ ContDiffOn ℝ ∞ (zeroPast u) (V ×ˢ Icc 0 s)) :
    ContDiffOn ℝ ∞ (zeroPast u) (O ×ˢ Icc 0 T) := by
  intro p hp
  by_cases ht : 0 < p.2
  · have hpQ : p ∈ O ×ˢ Ioo 0 S := ⟨hp.1,ht,hp.2.2.trans_lt hTS⟩
    have he : zeroPast u =ᶠ[𝓝 p] u := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds ht] with q hq
      exact zeroPast_of_pos u hq
    exact ((hu.contDiffAt ((hO.prod isOpen_Ioo).mem_nhds hpQ)).congr_of_eventuallyEq he).contDiffWithinAt
  · have ht0 : p.2 = 0 := le_antisymm (le_of_not_gt ht) hp.2.1
    obtain ⟨V,hV,hpV,hVO,hVC⟩ := exists_open_between_and_isCompact_closure isCompact_singleton hO
      (singleton_subset_iff.mpr hp.1)
    have hxV : p.1 ∈ V := hpV (mem_singleton _)
    obtain ⟨s,hs,_hsS,hsmooth⟩ := hInitial V hV hVC hVO
    have hn : V ×ˢ Iio s ∈ 𝓝 p := (hV.prod isOpen_Iio).mem_nhds ⟨hxV,by simpa only [ht0,mem_Iio] using hs⟩
    have hnW : V ×ˢ Iio s ∈ 𝓝[O ×ˢ Icc 0 T] p := mem_nhdsWithin_of_mem_nhds hn
    have hSmall : V ×ˢ Icc (0 : ℝ) s ∈ 𝓝[O ×ˢ Icc 0 T] p := by
      filter_upwards [hnW,self_mem_nhdsWithin] with q hq hqBig
      exact ⟨hq.1,hqBig.2.1,hq.2.le⟩
    exact (hsmooth p ⟨hxV,by simp only [ht0,mem_Icc]; exact ⟨le_rfl,hs.le⟩⟩).mono_of_mem_nhdsWithin hSmall

end Yau.F04Proof
