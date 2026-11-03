import Yau.Proofs.F01CompactJets

/-! An order-dependent estimate threshold is absorbed into each numerical
budget. The common domain and smoothness threshold is retained unchanged. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem common_threshold_jet_budgets_of_orderwise_thresholds
    {K : Set E} (hK : IsCompact K) (hUnique : UniqueDiffOn ℝ K)
    (f : ℕ → E → F) (N : ℕ)
    (hf : ∀ m, N ≤ m → ContDiffOn ℝ ∞ (f m) K)
    (hEst : ∀ k : ℕ, ∃ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ m, M ≤ m →
      ∀ x ∈ K, ‖iteratedFDerivWithin ℝ k (f m) K x‖ ≤ C) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ k m, N ≤ m →
      ∀ x ∈ K, ‖iteratedFDerivWithin ℝ k (f m) K x‖ ≤ C k := by
  classical
  have hex (k : ℕ) : ∃ D : ℝ, 0 < D ∧ ∀ m, N ≤ m →
      ∀ x ∈ K, ‖iteratedFDerivWithin ℝ k (f m) K x‖ ≤ D := by
    obtain ⟨M, C, hC, hbound⟩ := hEst k
    have hsmall (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (_ : N ≤ m) x,
        x ∈ K → ‖iteratedFDerivWithin ℝ k (f m) K x‖ ≤ B := by
      by_cases hm : N ≤ m
      · obtain ⟨B, hb⟩ := hK.exists_bound_of_continuousOn
          ((hf m hm).continuousOn_iteratedFDerivWithin
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) hUnique)
        exact ⟨max 0 B, le_max_left _ _, fun _ x hx => (hb x hx).trans (le_max_right _ _)⟩
      · exact ⟨0, le_refl 0, fun hn => False.elim (hm hn)⟩
    choose B hB hb using hsmall
    let D : ℝ := max C (∑ m ∈ Finset.range M, B m) + 1
    refine ⟨D, by dsimp only [D]; positivity, ?_⟩
    intro m hm x hx
    by_cases hMm : M ≤ m
    · exact (hbound m hMm x hx).trans (by dsimp only [D]; linarith [le_max_left C (∑ m ∈ Finset.range M, B m)])
    · have hsum : B m ≤ ∑ m ∈ Finset.range M, B m :=
        Finset.single_le_sum (fun l _ => hB l) (Finset.mem_range.mpr (Nat.lt_of_not_ge hMm))
      exact (hb m hm x hx).trans (by dsimp only [D]; linarith [le_max_right C (∑ m ∈ Finset.range M, B m)])
  choose C hC hb using hex
  exact ⟨C, hC, hb⟩

end Yau.NodeProofs.F01Aux
