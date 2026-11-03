import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators

noncomputable section
namespace Yau.NodeProofs.D02FiberLimitAux

/-- A fixed finite spanning tuple supplies constant coefficients for any
finite list of target vectors, including an empty list. -/
theorem exists_spanning_coefficients {K E ι κ : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype κ]
    (v : κ → E) (hspan : Submodule.span K (Set.range v) = ⊤) (b : ι → E) :
    ∃ C : ι → κ → K, ∀ i, ∑ a, C i a • v a = b i := by
  classical
  have hs := (span_range_eq_top_iff_surjective_fintypeLinearCombination K v).mp hspan
  choose C hC using fun i ↦ hs (b i)
  exact ⟨C, hC⟩

/-- The unconjugated evaluation equation reconstructs covector coordinates
using one fixed invertible matrix. -/
theorem matrix_inverse_reconstruct {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsUnit A.det) {η e : Fin n → ℂ} (he : A.mulVec η = e) :
    η = A⁻¹.mulVec e := by
  rw [← he, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]

end Yau.NodeProofs.D02FiberLimitAux
