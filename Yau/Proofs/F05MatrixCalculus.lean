import Yau.LeafProofs.L16CoefficientBounds

/-! Matrix entry evaluation uses the actual Frobenius norm, so coefficient
smoothness can be passed through a genuine continuous linear map. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

def F05MatrixEntry {n : ℕ} (i j : RIdx n) : Mat n →L[ℝ] ℝ :=
  ({ toFun := fun A => A i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Mat n →ₗ[ℝ] ℝ).mkContinuous 1
    (by intro A; rw [one_mul]; exact frobenius_entry_abs_le A i j)

theorem F05_contDiffOn_matrix_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {Q : Set E} {a : E → Mat n} (ha : ContDiffOn ℝ ∞ a Q) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun p => a p i j) Q := by
  exact (F05MatrixEntry i j).contDiff.contDiffOn.comp ha (fun _ _ => mem_univ _)

end Yau.Proofs.F05Aux
