import spec.CHAIN.CONTRACTS

/-! One positive sequence for finitely many chart families. The zeroth
budget also absorbs their metric comparison constants. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem exists_finite_uniform_budgets {ι : Type*} (s : Finset ι)
    (C : ι → ℕ → ℝ) (D : ι → ℝ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      (∀ i ∈ s, ∀ k, C i k ≤ B k) ∧ ∀ i ∈ s, D i ≤ B 0 := by
  classical
  let B : ℕ → ℝ := fun k => max 1 (∑ i ∈ s, max 0 (max (D i) (C i k))) + 1
  have hB : ∀ k, 0 < B k := by intro k; dsimp [B]; positivity
  have hsingle (i : ι) (hi : i ∈ s) (k : ℕ) :
      max 0 (max (D i) (C i k)) ≤ ∑ j ∈ s, max 0 (max (D j) (C j k)) :=
    Finset.single_le_sum (fun j _ => le_max_left (0 : ℝ) (max (D j) (C j k))) hi
  refine ⟨B, hB, ?_, ?_⟩
  · intro i hi k
    have h := (le_max_right (D i) (C i k)).trans
      ((le_max_right (0 : ℝ) (max (D i) (C i k))).trans (hsingle i hi k))
    dsimp [B]
    linarith [le_max_right (1 : ℝ) (∑ j ∈ s, max 0 (max (D j) (C j k)))]
  · intro i hi
    have h := (le_max_left (D i) (C i 0)).trans
      ((le_max_right (0 : ℝ) (max (D i) (C i 0))).trans (hsingle i hi 0))
    dsimp [B]
    linarith [le_max_right (1 : ℝ) (∑ j ∈ s, max 0 (max (D j) (C j 0)))]

end Yau.NodeProofs.F01Aux
