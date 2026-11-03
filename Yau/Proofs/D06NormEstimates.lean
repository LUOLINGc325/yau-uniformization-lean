import Yau.Proofs.D06Elementary

/-! Dimension-independent Frobenius/operator-norm estimates for the original
matrix factorization. The operator norm here is exactly `matOpNormR`. -/

open scoped Matrix

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint

variable {r : ℕ}

theorem frobSq_eq_sum_columnNormSq (A : Matrix (Fin r) (Fin r) ℂ) :
    frobSq A = ∑ j, ‖(WithLp.toLp 2 (fun i => A i j) : EuclideanSpace ℂ (Fin r))‖ ^ 2 := by
  rw [frobSq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (EuclideanSpace.norm_sq_eq
    (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace ℂ (Fin r))).symm

theorem matOpNormR_nonneg (A : Matrix (Fin r) (Fin r) ℂ) : 0 ≤ matOpNormR A :=
  norm_nonneg _

open scoped Matrix.Norms.L2Operator in
@[simp] theorem matOpNormR_conjTranspose (A : Matrix (Fin r) (Fin r) ℂ) :
    matOpNormR Aᴴ = matOpNormR A := by
  exact Matrix.l2_opNorm_conjTranspose A

/-- Summing the Euclidean operator bound over the columns loses no dimension
factor. -/
theorem frobSq_mul_le_left (A B : Matrix (Fin r) (Fin r) ℂ) :
    frobSq (A * B) ≤ matOpNormR A ^ 2 * frobSq B := by
  rw [frobSq_eq_sum_columnNormSq, frobSq_eq_sum_columnNormSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let v : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 (fun i => B i j)
  have hcol : Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) A v =
      (WithLp.toLp 2 (fun i => (A * B) i j) : EuclideanSpace ℂ (Fin r)) := by
    change Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) A
      (WithLp.toLp 2 (fun i => B i j)) = _
    rw [Matrix.toEuclideanCLM_toLp]
    rfl
  have h := (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) A).le_opNorm v
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [hcol, mul_pow] at hs
  exact hs

theorem frobSq_mul_le_right (A B : Matrix (Fin r) (Fin r) ℂ) :
    frobSq (A * B) ≤ frobSq A * matOpNormR B ^ 2 := by
  have h := frobSq_mul_le_left Bᴴ Aᴴ
  simpa only [← Matrix.conjTranspose_mul, frobSq_conjTranspose,
    matOpNormR_conjTranspose, mul_comm] using h

theorem factor_difference_bound (H Hθ K : Matrix (Fin r) (Fin r) ℂ)
    (hKH : K * H = 1) :
    frobSq (Hθ - H) ≤ frobSq (Hθ * K - 1) * matOpNormR H ^ 2 := by
  rw [factor_difference H Hθ K hKH]
  exact frobSq_mul_le_right _ _

theorem inverse_difference_bound (Hθ K Kθ : Matrix (Fin r) (Fin r) ℂ)
    (hKθHθ : Kθ * Hθ = 1) :
    frobSq (Kθ - K) ≤ matOpNormR Kθ ^ 2 * frobSq (Hθ * K - 1) := by
  rw [inverse_difference Hθ K Kθ hKθHθ]
  have h := frobSq_mul_le_left Kθ (1 - Hθ * K)
  rwa [frobSq_sub_comm 1 (Hθ * K)] at h

end Yau.NodeProofs.D06Aux
