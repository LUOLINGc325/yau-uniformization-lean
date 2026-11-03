import Yau.Proofs.V04HermitianCalculus

/-! The first negative moment is controlled by the third with a free
positive threshold. Empty cotangent indices are included in the same sums. -/

open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem trace_hermitianScalar (g : ℝ → ℝ) (A : CotangentMatrix n) (hA : A.IsHermitian) :
    (Matrix.trace (hermitianScalar g A)).re = ∑ i, g (hA.eigenvalues i) := by
  have hU : (hA.eigenvectorUnitary : CotangentMatrix n)ᴴ *
      (hA.eigenvectorUnitary : CotangentMatrix n) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  simp only [hermitianScalar, dif_pos hA]
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

theorem trace_matrixNegative_pow (A : CotangentMatrix n) (hA : A.IsHermitian) (k : ℕ) :
    (Matrix.trace (matrixNegative A ^ k)).re =
      ∑ i, max (-hA.eigenvalues i) 0 ^ k := by
  have he : matrixNegative A ^ k =
      hermitianScalar (fun x => max (-x) 0 ^ k) A := by
    rw [hermitianScalar_eq_cfc _ A hA,
      cfc_pow (fun x : ℝ => max (-x) 0) k A (by fun_prop) (show IsSelfAdjoint A from hA)]
    rw [matrixNegative, hermitianScalar_eq_cfc _ A hA]
  rw [he, trace_hermitianScalar _ A hA]

theorem trace_negative_one_le_cube (A : CotangentMatrix n) (hA : A.IsHermitian)
    {τ : ℝ} (hτ : 0 < τ) :
    (Matrix.trace (matrixNegative A)).re ≤
      (2 * n : ℕ) * τ + (Matrix.trace (matrixNegative A ^ 3)).re / τ ^ 2 := by
  have hfirst := trace_matrixNegative_pow A hA 1
  simp only [pow_one] at hfirst
  rw [hfirst, trace_matrixNegative_pow A hA 3]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    nonneg_le_threshold_add_cube (le_max_right (-hA.eigenvalues i) 0) hτ)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Finset.sum_div, two_mul] using hsum

end Yau.Blueprint.V04Proof
