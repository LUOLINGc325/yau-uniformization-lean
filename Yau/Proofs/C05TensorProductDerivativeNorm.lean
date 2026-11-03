import Yau.Proofs.C05CovariantProductLaplacian
import Yau.LeafProofs.L23TensorProductNorm
import Yau.LeafProofs.L23TensorNormLinear

/-! Intrinsic norm bounds for the true covariant tensor product rule. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n r s : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem covTensorPair_concatProduct (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A A' : CovTensor n r) (B B' : CovTensor n s) :
    covTensorPair G (tensorConcatProduct A B) (tensorConcatProduct A' B') =
      covTensorPair G A A' * covTensorPair G B B' :=
  tensorContraction_concatProduct G⁻¹ A A' B B'

def tensorDerivativeProductLeft (A : CovTensor n (r + 1)) (B : CovTensor n s) :
    CovTensor n (r + s + 1) :=
  fun v => tensorConcatProduct (fun u => A (Fin.cons (v 0) u)) B (fun j => v j.succ)

def tensorDerivativeProductRight (A : CovTensor n r) (B : CovTensor n (s + 1)) :
    CovTensor n (r + s + 1) :=
  fun v => tensorConcatProduct A (fun u => B (Fin.cons (v 0) u)) (fun j => v j.succ)

theorem tensorDerivativeProductLeft_normSq (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n (r + 1)) (B : CovTensor n s) :
    covTensorNormSq G (tensorDerivativeProductLeft A B) =
      covTensorNormSq G A * covTensorNormSq G B := by
  change covTensorPair G (tensorDerivativeProductLeft A B) (tensorDerivativeProductLeft A B) = _
  rw [covTensorPair_succ]
  change (∑ i : RIdx n, ∑ j : RIdx n, G⁻¹ i j * covTensorPair G
    (tensorConcatProduct (fun v => A (Fin.cons i v)) B)
    (tensorConcatProduct (fun v => A (Fin.cons j v)) B)) = _
  calc
    _ = ∑ i : RIdx n, ∑ j : RIdx n, G⁻¹ i j *
        (covTensorPair G (fun v => A (Fin.cons i v)) (fun v => A (Fin.cons j v)) *
          covTensorNormSq G B) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun t : ℝ => G⁻¹ i j * t)
        (covTensorPair_concatProduct G (fun v => A (Fin.cons i v))
          (fun v => A (Fin.cons j v)) B B)
    _ = (∑ i, ∑ j, G⁻¹ i j * covTensorPair G
        (fun v => A (Fin.cons i v)) (fun v => A (Fin.cons j v))) * covTensorNormSq G B := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by rw [← covTensorPair_succ, covTensorPair_self]

theorem tensorDerivativeProductRight_normSq (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n r) (B : CovTensor n (s + 1)) :
    covTensorNormSq G (tensorDerivativeProductRight A B) =
      covTensorNormSq G A * covTensorNormSq G B := by
  change covTensorPair G (tensorDerivativeProductRight A B) (tensorDerivativeProductRight A B) = _
  rw [covTensorPair_succ]
  change (∑ i : RIdx n, ∑ j : RIdx n, G⁻¹ i j * covTensorPair G
    (tensorConcatProduct A (fun v => B (Fin.cons i v)))
    (tensorConcatProduct A (fun v => B (Fin.cons j v)))) = _
  calc
    _ = ∑ i : RIdx n, ∑ j : RIdx n, G⁻¹ i j *
        (covTensorNormSq G A * covTensorPair G (fun v => B (Fin.cons i v))
          (fun v => B (Fin.cons j v))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun t : ℝ => G⁻¹ i j * t)
        (covTensorPair_concatProduct G A A (fun v => B (Fin.cons i v))
          (fun v => B (Fin.cons j v)))
    _ = covTensorNormSq G A * (∑ i, ∑ j, G⁻¹ i j * covTensorPair G
        (fun v => B (Fin.cons i v)) (fun v => B (Fin.cons j v))) := by
      simp only [Finset.mul_sum, mul_left_comm, mul_assoc]
    _ = _ := by rw [← covTensorPair_succ, covTensorPair_self]

theorem covariantD_concatProduct_split (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (z : ComplexVector n)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) z) :
    covariantD k c (fun w => tensorConcatProduct (A w) (B w)) z =
      tensorDerivativeProductLeft (covariantD k c A z) (B z) +
        tensorDerivativeProductRight (A z) (covariantD k c B z) := by
  funext v
  have hv : Fin.cons (v 0) (fun j => v j.succ) = v := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have hh := covariantD_concatProduct_cons k c A B z hA hB (v 0) (fun j => v j.succ)
  rw [hv] at hh
  exact hh

theorem covariantD_concatProduct_norm_le (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (z : ComplexVector n) (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) z) :
    Real.sqrt (covTensorNormSq G (covariantD k c (fun w => tensorConcatProduct (A w) (B w)) z)) ≤
      Real.sqrt (covTensorNormSq G (covariantD k c A z)) * Real.sqrt (covTensorNormSq G (B z)) +
        Real.sqrt (covTensorNormSq G (A z)) * Real.sqrt (covTensorNormSq G (covariantD k c B z)) := by
  rw [covariantD_concatProduct_split k c A B z hA hB]
  apply (sqrt_covTensorNormSq_add_le G hG _ _).trans_eq
  rw [tensorDerivativeProductLeft_normSq, tensorDerivativeProductRight_normSq,
    Real.sqrt_mul (covTensorNormSq_nonneg G hG (covariantD k c A z)),
    Real.sqrt_mul (covTensorNormSq_nonneg G hG (A z))]

end Yau.Proofs.C05Aux
