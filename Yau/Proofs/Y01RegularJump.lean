import Yau.Proofs.Y01PrimaryAlgebra
import Yau.Proofs.Y03SVD

/-! Every actual aligned jump used by the original Y06 solution is a unit. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ}

theorem matrix_inverse_isUnit {A : Herm n} (hA : IsUnit A) : IsUnit A⁻¹ := by
  exact Matrix.isUnit_nonsing_inv_iff.2 hA

theorem regular_alignedJump_isUnit
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {reg : ℕ → Prop} {w : ℕ → Fin n → ℝ}
    {macroIndex : ℕ → ℕ} {S : ℕ → ℝ} {C c : ℝ} {L : Changes n}
    (hL : ∀ k, reg k → ChangeAt (diagonal F tk E) w macroIndex S C c L k)
    {k : ℕ} (hk : reg k) :
    IsUnit (if reg (k + 1) then alignedJump E L k else 1) := by
  classical
  split_ifs with hk'
  · unfold alignedJump
    exact ((minus_change_isUnit hE (hL (k + 1) hk')).mul
      (unitary_isUnit (jump_unitary hE k))).mul
      (matrix_inverse_isUnit (plus_change_isUnit (hL k hk)))
  · exact isUnit_one

end Yau.Proofs.Y01Aux
