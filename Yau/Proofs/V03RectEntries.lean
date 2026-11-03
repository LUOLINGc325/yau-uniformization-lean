import Yau.Proofs.V03RectOperator

/-! Every actual matrix coefficient is bounded by the contract's native
Euclidean operator norm. In particular normalized-frame coefficients have
the bound one without any coordinate-frame bound assumption. -/

open scoped Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem matrix_entry_norm_le_rectOpNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (i : ι) (j : κ) : ‖A i j‖ ≤ rectOpNorm A := by
  classical
  let L := (Matrix.toEuclideanLin A).toContinuousLinearMap
  let v : EuclideanSpace ℂ κ := PiLp.single 2 j (1 : ℂ)
  have hv : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
  have hentry : ‖A i j‖ ≤ ‖L v‖ := by
    have hh := PiLp.norm_apply_le (L v) i
    change ‖(A *ᵥ Pi.single j (1 : ℂ)) i‖ ≤ ‖L v‖ at hh
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh
  have hop := L.le_opNorm v
  rw [hv, mul_one] at hop
  exact hentry.trans hop

theorem normalized_matrix_entry_norm_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1) (i : ι) (j : κ) :
    ‖U i j‖ ≤ 1 :=
  (matrix_entry_norm_le_rectOpNorm U i j).trans (rectOpNorm_le_one_of_gram U hU)

end Yau.Blueprint.V03Proof
