import Yau.Proofs.F01HolderComposition

/-! A uniform local Holder estimate on a fixed parabolic buffer gives
the original global numerical Holder predicate. Separated pairs are
controlled by the actual supremum bound. The constant precedes the field. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem local_holder_patching_budget {δ β C K : ℝ}
    (hδ : 0 < δ) (hβ : 0 ≤ β) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (f : Point n → E),
      (∀ p ∈ Q, ‖f p‖ ≤ C) →
      (∀ p ∈ Q, ∀ q ∈ Q, ‖p.1 - q.1‖ < δ → |p.2 - q.2| < δ ^ 2 →
        ‖f p - f q‖ ≤ K * holderWeight β p q) →
      HolderBound β Q f B := by
  let m := min (δ ^ β) ((δ ^ 2) ^ (β / 2))
  have hm : 0 < m := lt_min (Real.rpow_pos_of_pos hδ _)
    (Real.rpow_pos_of_pos (sq_pos_of_pos hδ) _)
  let B := 1 + C + K + 2 * C / m
  have hratio : 0 ≤ 2 * C / m := div_nonneg (mul_nonneg (by norm_num) hC) hm.le
  have hB : 0 < B := by dsimp only [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro Q f hSup hNear
  refine ⟨hB.le, fun p hp => (hSup p hp).trans (by dsimp only [B]; linarith), ?_⟩
  intro p hp q hq
  have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
  by_cases hSpace : ‖p.1 - q.1‖ < δ
  · by_cases hTime : |p.2 - q.2| < δ ^ 2
    · exact (hNear p hp q hq hSpace hTime).trans
        (mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith : K ≤ B) hw)
    · have hFar : m ≤ holderWeight β p q := by
        calc
          m ≤ (δ ^ 2) ^ (β / 2) := min_le_right _ _
          _ ≤ |p.2 - q.2| ^ (β / 2) :=
            Real.rpow_le_rpow (sq_nonneg _) (le_of_not_gt hTime) (by positivity)
          _ ≤ holderWeight β p q :=
            le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
      calc
        ‖f p - f q‖ ≤ ‖f p‖ + ‖f q‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hSup p hp) (hSup q hq)
        _ = (2 * C / m) * m := by field_simp; ring
        _ ≤ (2 * C / m) * holderWeight β p q := mul_le_mul_of_nonneg_left hFar hratio
        _ ≤ B * holderWeight β p q :=
          mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hw
  · have hFar : m ≤ holderWeight β p q := by
      calc
        m ≤ δ ^ β := min_le_left _ _
        _ ≤ ‖p.1 - q.1‖ ^ β := Real.rpow_le_rpow hδ.le (le_of_not_gt hSpace) hβ
        _ ≤ holderWeight β p q :=
          le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    calc
      ‖f p - f q‖ ≤ ‖f p‖ + ‖f q‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hSup p hp) (hSup q hq)
      _ = (2 * C / m) * m := by field_simp; ring
      _ ≤ (2 * C / m) * holderWeight β p q := mul_le_mul_of_nonneg_left hFar hratio
      _ ≤ B * holderWeight β p q :=
        mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hw

end Yau.NodeProofs.F01Aux
