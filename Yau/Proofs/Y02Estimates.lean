import Yau.Blueprint.Stages
import Yau.Proofs.Y02Algebra

/-! Coefficient estimates for polynomial realizations. -/

noncomputable section

namespace Yau.Proofs.Y02Aux

open Yau.Blueprint

/-- Each matrix entry is bounded by the Euclidean operator norm used in the contract. -/
theorem norm_entry_le_matOpNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : ‖A i j‖ ≤ matOpNorm A := by
  let e : ComplexVector n := WithLp.toLp 2 (Pi.single j 1)
  have he : ‖e‖ = 1 := by
    change ‖(PiLp.single 2 j (1 : ℂ) : EuclideanSpace ℂ (Fin n))‖ = 1
    simp
  have hentry : (Matrix.toEuclideanCLM (𝕜 := ℂ) A e) i = A i j := by
    change (WithLp.ofLp (Matrix.toEuclideanCLM (𝕜 := ℂ) A e)) i = A i j
    rw [Matrix.ofLp_toEuclideanCLM]
    simp [e, Matrix.mulVec, dotProduct, Pi.single_apply]
  calc
    ‖A i j‖ = ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) A e) i‖ := congrArg norm hentry.symm
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ = matOpNorm A := by rw [he, mul_one]; rfl

end Yau.Proofs.Y02Aux
