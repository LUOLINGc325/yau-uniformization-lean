import Yau.Proofs.F01FiniteTaylorComposition

/-! The native finite Taylor polynomial has a numerical Holder budget
on a fixed finite jet ball. The bound precedes every realized pair of
Taylor fields and keeps the full operator tensor norms. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem holderBound_dependent_pi {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    {Q : Set (Point n)} {β C : ℝ} {f : Point n → ∀ i, V i}
    (hC : 0 ≤ C) (hf : ∀ i, HolderBound β Q (fun p => f p i) C) :
    HolderBound β Q f C := by
  refine ⟨hC, ?_, ?_⟩
  · intro p hp
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro i
    exact (hf i).2.1 p hp
  · intro p hp q hq
    have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hw)).mpr
    intro i
    exact (hf i).2.2 p hp q hq

theorem holderBound_prod_max {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {Q : Set (Point n)} {β C D : ℝ} {f : Point n → E} {g : Point n → F}
    (hf : HolderBound β Q f C) (hg : HolderBound β Q g D) :
    HolderBound β Q (fun p => (f p, g p)) (max C D) := by
  refine ⟨hf.1.trans (le_max_left _ _), ?_, ?_⟩
  · intro p hp
    change max ‖f p‖ ‖g p‖ ≤ max C D
    exact max_le_max (hf.2.1 p hp) (hg.2.1 p hp)
  · intro p hp q hq
    have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
    change max ‖f p - f q‖ ‖g p - g q‖ ≤ _
    apply max_le
    · exact ((hf.2.2 p hp q hq).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw))
    · exact ((hg.2.2 p hp q hq).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hw))

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem finiteTaylorComposition_holder_budget (k : ℕ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (β : ℝ)
      (q : Point n → FiniteTaylorJet F G k) (p : Point n → FiniteTaylorJet E F k),
      (∀ j, HolderBound β Q (fun z => q z j) C) →
      (∀ j, HolderBound β Q (fun z => p z j) D) →
      HolderBound β Q (fun z => finiteTaylorComposition k (q z, p z)) B := by
  letI (j : Fin (k + 1)) :
      FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => F) G) :=
    continuousMultilinearMap_finiteDimensional j.val
  letI (j : Fin (k + 1)) :
      FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => E) F) :=
    continuousMultilinearMap_finiteDimensional j.val
  let A := max C D
  have hA : 0 ≤ A := hC.trans (le_max_left _ _)
  obtain ⟨B, hB, hb⟩ := compact_smooth_holder_composition_budget
    (n := n) (K := closedBall (0 : FiniteTaylorJet F G k × FiniteTaylorJet E F k) A)
    isOpen_univ (isCompact_closedBall _ _) (convex_closedBall _ _) (subset_univ _)
    (finiteTaylorComposition_smooth (E := E) (F := F) (G := G) k).contDiffOn hA
  refine ⟨B, hB, ?_⟩
  intro Q β q p hq hp
  have hj := holderBound_prod_max (holderBound_dependent_pi hC hq)
    (holderBound_dependent_pi hD hp)
  apply hb Q β (fun z => (q z, p z)) hj
  intro z hz
  exact mem_closedBall.mpr (by simpa only [dist_zero_right] using hj.2.1 z hz)

end Yau.NodeProofs.F01Aux
