import Yau.Proofs.V04WallErrorAlgebra
import Yau.Proofs.D05FrameBivector
import Yau.Proofs.V03SpatialHessianTransport

/-! The actual symplectic polynomial is invariant under the actual
cotangent chart transitions. No moving-centered coefficients are bounded
by assuming they form a continuous global trivialization. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {n : ℕ}

theorem canonicalBivector_eq_fromBlocks :
    (canonicalBivector : CotangentMatrix n) = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases hij : i = j <;> simp [canonicalBivector, Matrix.fromBlocks, Matrix.one_apply, hij, eq_comm]

theorem trace_fromBlocks (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem symplecticP_trace_formula (W : CotangentMatrix n) (hW : W.IsHermitian) :
    symplecticP W = -(1 / 2 : ℝ) *
      (Matrix.trace (W * canonicalBivector * Wᵀ * canonicalBivector)).re := by
  let A := W.toBlocks₁₁
  let B := W.toBlocks₁₂
  let C := W.toBlocks₂₂
  have hform : W = Matrix.fromBlocks A B Bᴴ C := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact (hW.apply (Sum.inr i) (Sum.inl j)).symm
    · rfl
  have hBtrace : Matrix.trace (Bᴴ * Bᵀ) = Matrix.trace (B * (Bᴴ)ᵀ) := by
    rw [← Matrix.trace_transpose (B * (Bᴴ)ᵀ)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hAC : Matrix.trace (C * Aᵀ) = Matrix.trace (A * Cᵀ) := by
    rw [← Matrix.trace_transpose (C * Aᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.trace_mul_comm]
  have hBsum : Matrix.trace (B * (Bᴴ)ᵀ) = ∑ i, ∑ j, B i j * star (B j i) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.conjTranspose_apply]
  have ht : Matrix.trace (W * canonicalBivector * Wᵀ * canonicalBivector) =
      -2 * (Matrix.trace (A * Cᵀ) - ∑ i, ∑ j, B i j * star (B j i)) := by
    rw [hform, canonicalBivector_eq_fromBlocks]
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_neg, Matrix.neg_mul, neg_neg, add_zero, zero_add, trace_fromBlocks,
      Matrix.trace_add, Matrix.trace_neg]
    rw [hBtrace, hAC, hBsum]
    ring
  let Z : ℂ := Matrix.trace (A * Cᵀ) - ∑ i, ∑ j, B i j * star (B j i)
  have hr : (Matrix.trace (W * canonicalBivector * Wᵀ * canonicalBivector)).re = -2 * Z.re := by
    rw [ht]
    change ((-2 : ℂ) * Z).re = -2 * Z.re
    rw [Complex.mul_re]
    norm_num
  change (Matrix.trace (W * canonicalBivector * Wᵀ * canonicalBivector)).re =
    -2 * symplecticP W at hr
  linarith

theorem symplecticP_symplectic_congruence (W P : CotangentMatrix n)
    (hW : W.IsHermitian) (hP : P * canonicalBivector * Pᵀ = canonicalBivector) :
    symplecticP (Pᴴ * W * P) = symplecticP W := by
  have hJ : (canonicalBivector : CotangentMatrix n)ᴴ = -canonicalBivector := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      by_cases hij : i = j <;> simp [canonicalBivector, Matrix.conjTranspose_apply, hij, eq_comm]
  have hPstar : (Pᴴ)ᵀ * canonicalBivector * Pᴴ = canonicalBivector := by
    have hp := congrArg (fun A : CotangentMatrix n => Aᴴ) hP
    simp only [Matrix.conjTranspose_mul, hJ, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at hp
    have hc : (Pᴴ)ᵀ = (Pᵀ)ᴴ := by ext i j; rfl
    rw [hc]
    simpa only [Matrix.mul_assoc] using hp
  have htr : Matrix.trace ((Pᴴ * W * P) * canonicalBivector *
      (Pᴴ * W * P)ᵀ * canonicalBivector) =
      Matrix.trace (W * canonicalBivector * Wᵀ * canonicalBivector) := by
    calc
      _ = Matrix.trace (Pᴴ * W * (P * canonicalBivector * Pᵀ) * Wᵀ * (Pᴴ)ᵀ * canonicalBivector) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Matrix.trace (Pᴴ * (W * canonicalBivector * Wᵀ * (Pᴴ)ᵀ * canonicalBivector)) := by
        rw [hP]
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((W * canonicalBivector * Wᵀ * (Pᴴ)ᵀ * canonicalBivector) * Pᴴ) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (W * canonicalBivector * Wᵀ * ((Pᴴ)ᵀ * canonicalBivector * Pᴴ)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPstar]
  rw [symplecticP_trace_formula _ (Matrix.isHermitian_conjTranspose_mul_mul P hW), symplecticP_trace_formula W hW, htr]

variable {q : ℕ} {X : KahlerManifold n}

theorem symplecticP_spatialHessian_fixed_chart
    (b : CotangentPoint X.manifold → ℝ) (x : Pt X) {y : CotangentPoint X.manifold}
    (hy : y ∈ cotangentSource x)
    (hb : ContDiffAt ℝ 2 (fun z => b (cotangentChartInv x z)) (cotangentChart x y)) :
    symplecticP (spatialHessian b y) =
      symplecticP (leviMatrix (fun z => b (cotangentChartInv x z)) (cotangentChart x y) cotangentDir) := by
  rw [spatialHessian_in_fixed_chart b x hy hb]
  exact symplecticP_symplectic_congruence _ _ (leviMatrix_isHermitian hb cotangentDir)
    (D05Proof.cotangentTransition_symplectic y.1 x y (mem_extChartAt_source y.1) hy)

end Yau.Blueprint.V04Proof.WallErrorAux
