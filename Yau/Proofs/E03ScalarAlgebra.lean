import spec.CHAIN.CONTRACTS

/-! SOURCE-ONLY E03 candidate. These are elementary transformations, not E03 itself. -/

noncomputable section
open scoped Topology
open Filter Set

namespace Yau.NodeProofs.E03Aux

theorem scalar_gap_test_rearrangement (a R dφ dtφ : ℝ)
    (h : a * (R - dφ) ≤ R - dtφ) :
    dtφ ≤ a * dφ + (1 - a) * R := by
  nlinarith

theorem exists_shorter_comparison_horizon {t T : ℝ} (ht : 0 < t) (htT : t < T) :
    ∃ S : ℝ, 0 < S ∧ t < S ∧ S < T := by
  obtain ⟨S, htS, hST⟩ := exists_between htT
  exact ⟨S, ht.trans htS, htS, hST⟩

theorem upperSemicontinuousWithinAt_of_continuous_majorant_at_zero
    {A : Type*} [TopologicalSpace A] (f g : A → ℝ) (S : Set A) (p : A)
    (hf : f p = 0) (hg : g p = 0) (hc : ContinuousWithinAt g S p)
    (hle : ∀ᶠ q in 𝓝[S] p, f q ≤ g q) :
    UpperSemicontinuousWithinAt f S p := by
  intro a ha
  have hga : g p < a := by simpa only [hf, hg] using ha
  have hnear : ∀ᶠ q in 𝓝[S] p, g q < a := hc.eventually (gt_mem_nhds hga)
  filter_upwards [hle, hnear] with q hq hq'
  exact hq.trans_lt hq'

end Yau.NodeProofs.E03Aux
