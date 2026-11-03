import Yau.Proofs.F01HolderComposition

/-! Actual bounded bilinear contractions preserve the original Holder
predicate with a numerical budget before the two field realizations. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem holderBound_bilinear {Q : Set (Point n)} {β C D : ℝ}
    {f : Point n → E} {g : Point n → F}
    (hf : HolderBound β Q f C) (hg : HolderBound β Q g D)
    (L : E →L[ℝ] F →L[ℝ] G) :
    HolderBound β Q (fun p => L (f p) (g p)) (2 * ‖L‖ * C * D) := by
  have hnorm (x : E) (y : F) : ‖L x y‖ ≤ ‖L‖ * ‖x‖ * ‖y‖ :=
    ((L x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (L.le_opNorm x) (norm_nonneg y))
  have hN : 0 ≤ ‖L‖ := ContinuousLinearMap.opNorm_nonneg L
  refine ⟨mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hN) hf.1) hg.1, ?_, ?_⟩
  · intro p hp
    calc
      _ ≤ ‖L‖ * ‖f p‖ * ‖g p‖ := hnorm _ _
      _ ≤ ‖L‖ * C * D := mul_le_mul
        (mul_le_mul_of_nonneg_left (hf.2.1 p hp) hN) (hg.2.1 p hp)
        (norm_nonneg _) (mul_nonneg hN hf.1)
      _ ≤ 2 * ‖L‖ * C * D := by nlinarith [mul_nonneg (mul_nonneg hN hf.1) hg.1]
  · intro p hp q hq
    have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
    have he : L (f p) (g p) - L (f q) (g q) =
        L (f p - f q) (g p) + L (f q) (g p - g q) := by
      simp only [map_sub, sub_apply]
      abel
    rw [he]
    calc
      _ ≤ ‖L (f p - f q) (g p)‖ + ‖L (f q) (g p - g q)‖ := norm_add_le _ _
      _ ≤ ‖L‖ * ‖f p - f q‖ * ‖g p‖ + ‖L‖ * ‖f q‖ * ‖g p - g q‖ :=
        add_le_add (hnorm _ _) (hnorm _ _)
      _ ≤ ‖L‖ * (C * holderWeight β p q) * D +
          ‖L‖ * C * (D * holderWeight β p q) := add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left (hf.2.2 p hp q hq) hN)
          (hg.2.1 p hp) (norm_nonneg _) (mul_nonneg hN (mul_nonneg hf.1 hw)))
        (mul_le_mul (mul_le_mul_of_nonneg_left (hf.2.1 q hq) hN)
          (hg.2.2 p hp q hq) (norm_nonneg _) (mul_nonneg hN hf.1))
      _ = (2 * ‖L‖ * C * D) * holderWeight β p q := by ring

end Yau.NodeProofs.F01Aux
