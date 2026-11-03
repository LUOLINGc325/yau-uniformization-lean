import Yau.Proofs.F01BackgroundInitialHolder

/-! Closure of the original numerical Holder predicate under actual
continuous linear maps and maps with a proved supremum/Lipschitz budget.
The output constant is fixed before the function realization. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem holderBound_continuousLinearMap {f : Point n → E} {Q : Set (Point n)} {β C : ℝ}
    (hf : HolderBound β Q f C) (L : E →L[ℝ] F) :
    HolderBound β Q (fun p => L (f p)) (‖L‖ * C) := by
  refine ⟨mul_nonneg (norm_nonneg _) hf.1, ?_, ?_⟩
  · intro p hp
    exact (L.le_opNorm (f p)).trans (mul_le_mul_of_nonneg_left (hf.2.1 p hp) (norm_nonneg _))
  · intro p hp q hq
    rw [← map_sub]
    exact (L.le_opNorm (f p - f q)).trans
      ((mul_le_mul_of_nonneg_left (hf.2.2 p hp q hq) (norm_nonneg _)).trans_eq (by ring))

theorem holderBound_add {f g : Point n → E} {Q : Set (Point n)} {β C D : ℝ}
    (hf : HolderBound β Q f C) (hg : HolderBound β Q g D) :
    HolderBound β Q (fun p => f p + g p) (C + D) := by
  refine ⟨add_nonneg hf.1 hg.1, ?_, ?_⟩
  · intro p hp
    exact (norm_add_le _ _).trans (add_le_add (hf.2.1 p hp) (hg.2.1 p hp))
  · intro p hp q hq
    have he : f p + g p - (f q + g q) = (f p - f q) + (g p - g q) := by abel
    rw [he]
    exact (norm_add_le _ _).trans
      ((add_le_add (hf.2.2 p hp q hq) (hg.2.2 p hp q hq)).trans_eq (by ring))

theorem holder_lipschitz_composition_budget {φ : E → F} {S : Set E} {M L C : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hSup : ∀ x ∈ S, ‖φ x‖ ≤ M)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖φ x - φ y‖ ≤ L * ‖x - y‖) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (β : ℝ) (f : Point n → E),
      HolderBound β Q f C → Set.MapsTo f Q S → HolderBound β Q (fun p => φ (f p)) B := by
  let B := 1 + M + L * C
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro Q β f hf hm
  refine ⟨hB.le, ?_, ?_⟩
  · intro p hp
    exact (hSup _ (hm hp)).trans (by dsimp only [B]; linarith [mul_nonneg hL hC])
  · intro p hp q hq
    have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
    calc
      _ ≤ L * ‖f p - f q‖ := hLip _ (hm hp) _ (hm hq)
      _ ≤ L * (C * holderWeight β p q) := mul_le_mul_of_nonneg_left (hf.2.2 p hp q hq) hL
      _ = (L * C) * holderWeight β p q := by ring
      _ ≤ B * holderWeight β p q := mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hw

end Yau.NodeProofs.F01Aux
