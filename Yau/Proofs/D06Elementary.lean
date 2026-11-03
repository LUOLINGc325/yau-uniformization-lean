import spec.CHAIN.CONTRACTS

/-! Algebraic identities and the empty-rank case of the boundary factorization.
These lemmas use the exact Frobenius seminorm and Euclidean operator norm in
`Yau.Blueprint.Nodes`; no factorization input is assumed. -/

open scoped Matrix ComplexConjugate ContDiff
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint

variable {r : ℕ}

theorem frobSq_nonneg (A : Matrix (Fin r) (Fin r) ℂ) : 0 ≤ frobSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

@[simp] theorem frobSq_zero : frobSq (0 : Matrix (Fin r) (Fin r) ℂ) = 0 := by
  simp [frobSq]

@[simp] theorem frobSq_neg (A : Matrix (Fin r) (Fin r) ℂ) :
    frobSq (-A) = frobSq A := by
  simp [frobSq]

theorem frobSq_sub_comm (A B : Matrix (Fin r) (Fin r) ℂ) :
    frobSq (A - B) = frobSq (B - A) := by
  rw [← neg_sub B A, frobSq_neg]

@[simp] theorem frobSq_conjTranspose (A : Matrix (Fin r) (Fin r) ℂ) :
    frobSq Aᴴ = frobSq A := by
  simp only [frobSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

@[simp] theorem halfSobolevSq_const (A : Matrix (Fin r) (Fin r) ℂ) :
    halfSobolevSq (fun _ => A) = 0 := by
  simp [halfSobolevSq]

/-- The normalized Hardy basis matrix and a right inverse recover the original
Gram matrix. The same identity is used pointwise for their boundary traces. -/
theorem factor_of_normalized_inverse (L P Q : Matrix (Fin r) (Fin r) ℂ)
    (hPQ : P * Q = 1) (hboundary : Pᴴ * L * P = 1) : L = Qᴴ * Q := by
  calc
    L = (P * Q)ᴴ * L * (P * Q) := by rw [hPQ]; simp
    _ = Qᴴ * (Pᴴ * L * P) * Q := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Qᴴ * Q := by rw [hboundary]; simp

/-- The first difference identity in the source proof. -/
theorem factor_difference (H Hθ K : Matrix (Fin r) (Fin r) ℂ)
    (hKH : K * H = 1) : Hθ - H = (Hθ * K - 1) * H := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hKH, Matrix.mul_one]

/-- The inverse difference identity in the source proof. -/
theorem inverse_difference (Hθ K Kθ : Matrix (Fin r) (Fin r) ℂ)
    (hKθHθ : Kθ * Hθ = 1) : Kθ - K = Kθ * (1 - Hθ * K) := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hKθHθ, Matrix.one_mul]

/-- The algebraic symmetrization behind the factor one-half in both final
seminorm bounds. This is a matrix identity before taking a trace or average. -/
theorem symmetric_relative_difference (A B X Y : Matrix (Fin r) (Fin r) ℂ)
    (hAX : A * X = 1) (hXA : X * A = 1) (hBY : B * Y = 1) :
    (B - A) * X * (B - A) * Y = (B * X - 1) + (A * Y - 1) := by
  have h₁ : B * X * B * Y = B * X := by
    rw [Matrix.mul_assoc (B * X) B Y, hBY, Matrix.mul_one]
  have h₂ : A * X * B * Y = 1 := by rw [hAX, Matrix.one_mul, hBY]
  have h₃ : B * X * A * Y = 1 := by
    rw [Matrix.mul_assoc B X A, hXA, Matrix.mul_one, hBY]
  have h₄ : A * X * A * Y = A * Y := by rw [hAX, Matrix.one_mul]
  calc
    (B - A) * X * (B - A) * Y =
        B * X * B * Y - A * X * B * Y - B * X * A * Y + A * X * A * Y := by
      noncomm_ring
    _ = (B * X - 1) + (A * Y - 1) := by rw [h₁, h₂, h₃, h₄]; abel

/-- The original factorization obligation includes rank zero. -/
theorem boundaryFactorization_zero : BoundaryFactorization 0 := by
  intro L m M hm hmM _ _ _
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro ζ hζ
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · intro t
    exact Subsingleton.elim _ _
  · intro ζ hζ
    constructor
    · simp [matOpNormR]
    · simp [matOpNormR]
  · change halfSobolevSq (fun _ : ℝ => (0 : Matrix (Fin 0) (Fin 0) ℂ)) ≤ _
    rw [halfSobolevSq_const]
    exact bot_le
  · change halfSobolevSq (fun _ : ℝ => (0 : Matrix (Fin 0) (Fin 0) ℂ)) ≤ _
    rw [halfSobolevSq_const]
    exact bot_le

end Yau.NodeProofs.D06Aux
