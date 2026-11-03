import Yau.Proofs.E02HermitianQuadratic

open Matrix
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Exact real contraction of a finite sum with non-complex weights. -/
theorem real_quadratic_sum_smul {n m : ℕ} (α : Fin m → ℝ) (A : Fin m → Herm n)
    (v : Fin n → ℂ) :
    (star v ⬝ᵥ ((∑ i, (α i : ℂ) • A i)*ᵥv)).re =
      ∑ i, α i*(star v ⬝ᵥ (A i*ᵥv)).re := by
  simp only [Matrix.sum_mulVec,dotProduct_sum,Complex.re_sum,Matrix.smul_mulVec,
    dotProduct_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

theorem weighted_sum_isHermitian {n m : ℕ} (α : Fin m → ℝ) (A : Fin m → Herm n)
    (hA : ∀ i, (A i).IsHermitian) : (∑ i, (α i : ℂ) • A i).IsHermitian := by
  change (∑ i, (α i : ℂ) • A i)ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ((hA i).smul (by simp [isSelfAdjoint_iff] : IsSelfAdjoint (α i : ℂ))).eq

theorem weighted_sum_posSemidef {n m : ℕ} (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (A : Fin m → Herm n) (hA : ∀ i, (A i).PosSemidef) :
    (∑ i, (α i : ℂ) • A i).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun i _ => ((hA i).smul (RCLike.ofReal_nonneg.mpr (hα i))).nonneg)

end Yau.NodeProofs.E02Aux
