import Yau.Proofs.V04FactorColumns

/-! A finite Hilbert-Schmidt estimate for the actual trace-square error.
All operator products retain their order. The uniform bound is supplied
by actual matrix entries, with no positive-rank assumption. -/

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem cotangentMatrixHS_add (A B : CotangentMatrix n) :
    cotangentMatrixHS (A + B) = cotangentMatrixHS A + cotangentMatrixHS B := rfl

theorem matrixFrobSq_mul_le (A B : CotangentMatrix n) :
    matrixFrobSq (A * B) ≤ matrixFrobSq A * matrixFrobSq B := by
  let v : CotangentIndex n → EuclideanSpace ℂ (CotangentIndex n) :=
    fun j => WithLp.toLp 2 (fun k => B k j)
  calc
    _ = ∑ j, ‖Matrix.toEuclideanLin A (v j)‖ ^ 2 := by
      simp only [matrixFrobSq, EuclideanSpace.norm_sq_eq, v, Matrix.toLpLin_apply,
        Matrix.mulVec, dotProduct, Matrix.mul_apply, PiLp.toLp_apply]
      exact Finset.sum_comm
    _ ≤ ∑ j, matrixFrobSq A * ‖v j‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ => matrix_vector_norm_sq_le_frob A (v j))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [v, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply, matrixFrobSq]
      exact Finset.sum_comm

theorem matrixHS_norm_mul_le (A B : CotangentMatrix n) :
    ‖cotangentMatrixHS (A * B)‖ ≤ ‖cotangentMatrixHS A‖ * ‖cotangentMatrixHS B‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, cotangentMatrixHS_norm_sq, cotangentMatrixHS_norm_sq, cotangentMatrixHS_norm_sq]
  exact matrixFrobSq_mul_le A B

theorem matrixHS_norm_le_of_entries (A : CotangentMatrix n) {M : ℝ} (hM : 0 ≤ M)
    (hentry : ∀ i j, ‖A i j‖ ≤ M) : ‖cotangentMatrixHS A‖ ≤ (2 * n : ℕ) * M := by
  have hs : matrixFrobSq A ≤ (2 * n : ℕ) * ((2 * n : ℕ) * M ^ 2) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
        (sq_le_sq₀ (norm_nonneg _) hM).mpr (hentry i j)))
    simpa only [matrixFrobSq, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, two_mul] using hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hM)).mp
  rw [cotangentMatrixHS_norm_sq]
  exact hs.trans_eq (by ring)

theorem trace_square_difference_le (T S N : CotangentMatrix n) (hT : T.IsHermitian)
    {M : ℝ} (hM : 0 ≤ M) (hTb : ‖cotangentMatrixHS T‖ ≤ M)
    (hSb : ‖cotangentMatrixHS S‖ ≤ M) (hNb : ‖cotangentMatrixHS N‖ ≤ M) :
    |(Matrix.trace (T * (S ^ 2 - N ^ 2))).re| ≤
      2 * M ^ 2 * ‖cotangentMatrixHS (S - N)‖ := by
  have htr : |(Matrix.trace (T * (S ^ 2 - N ^ 2))).re| ≤
      ‖cotangentMatrixHS T‖ * ‖cotangentMatrixHS (S ^ 2 - N ^ 2)‖ := by
    rw [← cotangentMatrixHS_inner T _ hT]
    exact abs_real_inner_le_norm _ _
  have heq : S ^ 2 - N ^ 2 = S * (S - N) + (S - N) * N := by noncomm_ring
  have hd : ‖cotangentMatrixHS (S ^ 2 - N ^ 2)‖ ≤ 2 * M * ‖cotangentMatrixHS (S - N)‖ := by
    rw [heq, cotangentMatrixHS_add]
    calc
      _ ≤ ‖cotangentMatrixHS (S * (S - N))‖ + ‖cotangentMatrixHS ((S - N) * N)‖ := norm_add_le _ _
      _ ≤ ‖cotangentMatrixHS S‖ * ‖cotangentMatrixHS (S - N)‖ +
          ‖cotangentMatrixHS (S - N)‖ * ‖cotangentMatrixHS N‖ :=
        add_le_add (matrixHS_norm_mul_le _ _) (matrixHS_norm_mul_le _ _)
      _ ≤ M * ‖cotangentMatrixHS (S - N)‖ + ‖cotangentMatrixHS (S - N)‖ * M :=
        add_le_add (mul_le_mul_of_nonneg_right hSb (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hNb (norm_nonneg _))
      _ = _ := by ring
  exact (htr.trans (mul_le_mul hTb hd (norm_nonneg _) hM)).trans_eq (by ring)

end Yau.Blueprint.V04Proof
