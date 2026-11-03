import Yau.Proofs.Y01PrimaryCoordinates
import Yau.Proofs.Y03Frames

/-! The primary derivative retains the polynomial bounds of the same
aligned changes, including the previous regular endpoint at a bad start. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

theorem primary_change_norm_bound
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {reg : ℕ → Prop} {L : Changes n} {B : ℕ → ℝ}
    (hmono : Monotone B) (hB : ∀ k, 2 ≤ B k)
    (hminus : ∀ k, reg k → matOpNorm (L.minus k) + matOpNorm (L.minus k)⁻¹ ≤ B k)
    (hplus : ∀ k, reg k → matOpNorm (L.plus k) + matOpNorm (L.plus k)⁻¹ ≤ B k)
    (k : ℕ) :
    matOpNorm (primaryDerivative reg E L k) +
        matOpNorm (primaryDerivative reg E L k)⁻¹ ≤ B k := by
  classical
  unfold primaryDerivative
  split_ifs with hk hp
  · rw [Matrix.mul_inv_rev, unitary_conjTranspose_inverse (hE k).2.2.1,
      matOpNorm_mul_unitary (unitary_conjTranspose (hE k).2.2.1),
      matOpNorm_unitary_mul (hE k).2.2.1]
    exact hminus k hk
  · rw [Matrix.mul_inv_rev, unitary_conjTranspose_inverse (hE (k - 1)).2.2.2.1,
      matOpNorm_mul_unitary (unitary_conjTranspose (hE (k - 1)).2.2.2.1),
      matOpNorm_unitary_mul (hE (k - 1)).2.2.2.1]
    exact (hplus (k - 1) hp.2).trans (hmono (by omega))
  · simp only [inv_one]
    linarith [matOpNorm_one_le (n := n), hB k]

end Yau.Proofs.Y01Aux
