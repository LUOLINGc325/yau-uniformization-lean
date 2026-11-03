import Yau.Proofs.F01HolderComposition

/-! Scalar multiplication preserves the actual Holder inequalities
with an explicit numerical product budget. No norm on a nested operator
space is needed for a symmetric-matrix target. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem holderBound_scalar_smul_product {Q : Set (Point n)} {β C D : ℝ}
    {f : Point n → ℝ} {g : Point n → F}
    (hf : HolderBound β Q f C) (hg : HolderBound β Q g D) :
    HolderBound β Q (fun p => f p • g p) (2 * C * D) := by
  refine ⟨mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hf.1) hg.1, ?_, ?_⟩
  · intro p hp
    rw [norm_smul]
    exact (mul_le_mul (hf.2.1 p hp) (hg.2.1 p hp) (norm_nonneg _) hf.1).trans
      (by nlinarith [mul_nonneg hf.1 hg.1])
  · intro p hp q hq
    have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
    have he : f p • g p - f q • g q = (f p - f q) • g p + f q • (g p - g q) := by module
    rw [he]
    calc
      _ ≤ ‖(f p - f q) • g p‖ + ‖f q • (g p - g q)‖ := norm_add_le _ _
      _ = ‖f p - f q‖ * ‖g p‖ + ‖f q‖ * ‖g p - g q‖ := by rw [norm_smul, norm_smul]
      _ ≤ (C * holderWeight β p q) * D + C * (D * holderWeight β p q) :=
        add_le_add
          (mul_le_mul (hf.2.2 p hp q hq) (hg.2.1 p hp) (norm_nonneg _) (mul_nonneg hf.1 hw))
          (mul_le_mul (hf.2.1 q hq) (hg.2.2 p hp q hq) (norm_nonneg _) hf.1)
      _ = (2 * C * D) * holderWeight β p q := by ring

end Yau.NodeProofs.F01Aux
