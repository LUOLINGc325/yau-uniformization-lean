import spec.CHAIN.CONTRACTS

/-! One positive rescaling factor for a finite buffered atlas. It may depend
on fixed L, as allowed for the bounded-geometry background; it is independent
of the chart center and of derivative order. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem exists_chart_scale_budget {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i) {L M : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ (∀ i ∈ s, c ≤ r i / 12) ∧ 2 * c * M / L ≤ 1 / 2 := by
  let rmin := s.inf' hs r
  have hrmin : 0 < rmin := (Finset.lt_inf'_iff hs).mpr hr
  let c := min 1 (min (rmin / 12) (L / (8 * (M + 1))))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcr : c ≤ rmin / 12 := (min_le_right _ _).trans (min_le_left _ _)
  have hcM : c ≤ L / (8 * (M + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, min_le_left _ _, ?_, ?_⟩
  · intro i hi
    exact hcr.trans (div_le_div_of_nonneg_right (Finset.inf'_le r hi) (by norm_num))
  · have hb : c * (8 * (M + 1)) ≤ L :=
      (le_div_iff₀ (by positivity : 0 < 8 * (M + 1))).mp hcM
    apply (div_le_iff₀ hL).mpr
    nlinarith [mul_nonneg hc.le hM]

end Yau.NodeProofs.F01Aux
