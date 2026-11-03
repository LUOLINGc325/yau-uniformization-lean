import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! Determinant control of the relative inverse trace. The spectral
argument includes the empty index type without selecting an eigenvalue. -/

open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eigenvalues_one_le_of_sub_one_posSemidef
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hlo : (A - 1).PosSemidef) (i : ι) :
    1 ≤ hA.eigenvalues i := by
  let v : ι → ℂ := WithLp.ofLp (hA.eigenvectorBasis i)
  have hv : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have hp := hlo.re_dotProduct_nonneg v
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, map_sub] at hp
  rw [hv, RCLike.one_re, ← hA.eigenvalues_eq i] at hp
  linarith

theorem real_le_prod_of_one_le (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i) (i : ι) :
    a i ≤ ∏ j, a j := by
  have hp : 1 ≤ ∏ j ∈ Finset.univ.erase i, a j :=
    Finset.one_le_prod₀ (fun j _ => ha j)
  calc
    a i ≤ a i * ∏ j ∈ Finset.univ.erase i, a j :=
      le_mul_of_one_le_right (zero_le_one.trans (ha i)) hp
    _ = ∏ j, a j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)

theorem trace_le_card_mul_det_of_sub_one_posSemidef
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hlo : (A - 1).PosSemidef) :
    (Matrix.trace A).re ≤ (Fintype.card ι : ℝ) * A.det.re := by
  have hEigen := eigenvalues_one_le_of_sub_one_posSemidef hA hlo
  have hdet : A.det.re = ∏ i, hA.eigenvalues i := by
    change RCLike.re A.det = _
    rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  have htrace : (Matrix.trace A).re = ∑ i, hA.eigenvalues i := by
    change RCLike.re (Matrix.trace A) = _
    rw [hA.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum, RCLike.ofReal_re]
  rw [hdet, htrace]
  calc
    ∑ i, hA.eigenvalues i ≤ ∑ _i : ι, ∏ j, hA.eigenvalues j :=
      Finset.sum_le_sum fun i _ => real_le_prod_of_one_le _ hEigen i
    _ = _ := by simp

end Yau.Blueprint.V04Proof.WallErrorAux
