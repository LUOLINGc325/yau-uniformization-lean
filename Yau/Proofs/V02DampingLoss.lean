import Yau.Proofs.V02CircleTaylor

/-! The auxiliary damping affects the quadratic test by a quantity that
vanishes with its logarithmic center loss and boundary mean loss. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

theorem damping_center_square_loss {t η : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hloss : -Real.log t ≤ η) : 0 ≤ 1 - t ^ 2 ∧ 1 - t ^ 2 ≤ 2 * η := by
  have hlog := Real.log_le_sub_one_of_pos ht
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (1 - t)]

theorem damped_quadratic_error {t S A B e C W ε η M₀ M₁ : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hloss : -Real.log t ≤ η)
    (hS : |S| ≤ M₀) (hM₀ : 0 ≤ M₀)
    (hboundary : A - B ≤ M₁ * η) (henergy : e ≤ C * W) (hε : 0 ≤ ε) :
    S - B - ε * C * W ≤ -(A - t ^ 2 * S + ε * e) + (2 * M₀ + M₁) * η := by
  have hl := damping_center_square_loss ht ht1 hloss
  have hcenter : (1 - t ^ 2) * S ≤ 2 * M₀ * η := by
    calc
      (1 - t ^ 2) * S ≤ (1 - t ^ 2) * M₀ :=
        mul_le_mul_of_nonneg_left (le_abs_self S |>.trans hS) hl.1
      _ ≤ (2 * η) * M₀ := mul_le_mul_of_nonneg_right hl.2 hM₀
      _ = 2 * M₀ * η := by ring
  have he := mul_le_mul_of_nonneg_left henergy hε
  nlinarith

end Yau.Blueprint.V02Proof
