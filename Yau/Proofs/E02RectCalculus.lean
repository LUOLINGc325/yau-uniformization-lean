import Yau.Proofs.E02MatrixBasic
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Analysis.LocallyConvex.WithSeminorms

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance rectNormable (n m : ℕ) : IsNormableSpace ℝ (Rect n m) :=
  inferInstanceAs (IsNormableSpace ℝ (Fin n → Fin m → ℂ))

/-- Rectangular multiplication is genuinely bounded for the native
entrywise norm; the factor is the actual number of contracted entries. -/
theorem rect_mul_norm_le (l m n : ℕ) (A : Rect l m) (B : Rect m n) :
    ‖A*B‖ ≤ (m:ℝ)*‖A‖*‖B‖ := by
  apply (Matrix.norm_le_iff (show 0 ≤ (m:ℝ)*‖A‖*‖B‖ by positivity)).mpr
  intro i k
  rw [Matrix.mul_apply]
  calc
    ‖∑ j, A i j*B j k‖ ≤ ∑ j, ‖A i j*B j k‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin m, ‖A‖*‖B‖ := Finset.sum_le_sum fun j _ => by
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

def rectMulLinear (l m n : ℕ) : Rect l m →ₗ[ℝ] Rect m n →ₗ[ℝ] Rect l n :=
  _root_.mulLinearMap (l := Fin l) (m := Fin m) (n := Fin n) (A := ℂ) ℝ

def rectMulCLM (l m n : ℕ) : Rect l m →L[ℝ] Rect m n →L[ℝ] Rect l n :=
  (rectMulLinear l m n).mkContinuous₂ (m:ℝ) (fun A B => rect_mul_norm_le l m n A B)

@[simp] theorem rectMulCLM_apply (l m n : ℕ) (A : Rect l m) (B : Rect m n) :
    rectMulCLM l m n A B = A*B := rfl

def rectAdjointLinear (n m : ℕ) : Rect n m →ₗ[ℝ] Rect m n where
  toFun := Matrix.conjTranspose
  map_add' := Matrix.conjTranspose_add
  map_smul' c A := by simp

def rectAdjointCLM (n m : ℕ) : Rect n m →L[ℝ] Rect m n :=
  (rectAdjointLinear n m).mkContinuous 1 (fun A => by simp [rectAdjointLinear])

@[simp] theorem rectAdjointCLM_apply (n m : ℕ) (A : Rect n m) :
    rectAdjointCLM n m A = Aᴴ := rfl

/-- The derivative field of the actual Gram map is itself linear. -/
def gramHessian (n m : ℕ) : Rect n m →L[ℝ] Rect n m →L[ℝ] Herm n :=
  ((rectMulCLM n m n).precompR (Rect n m)).flip (rectAdjointCLM n m) +
    (((rectMulCLM n m n).precompL (Rect n m)) (ContinuousLinearMap.id ℝ (Rect n m))).comp
      (rectAdjointCLM n m)

theorem gramHessian_apply (n m : ℕ) (M Z : Rect n m) :
    gramHessian n m M Z = M*Zᴴ+Z*Mᴴ := rfl

theorem gram_hasFDerivAt {n m : ℕ} (M : Rect n m) :
    HasFDerivAt (fun N : Rect n m => N*Nᴴ) (gramHessian n m M) M := by
  exact (rectMulCLM n m n).hasFDerivAt_of_bilinear (hasFDerivAt_id M)
    ((rectAdjointCLM n m).hasFDerivAt)

theorem gram_fderiv {n m : ℕ} (M : Rect n m) :
    fderiv ℝ (fun N : Rect n m => N*Nᴴ) M = gramHessian n m M :=
  (gram_hasFDerivAt M).fderiv

theorem gram_second_fderiv {n m : ℕ} (M : Rect n m) :
    fderiv ℝ (fderiv ℝ (fun N : Rect n m => N*Nᴴ)) M = gramHessian n m := by
  have hF : fderiv ℝ (fun N : Rect n m => N*Nᴴ) = gramHessian n m := by
    funext N
    exact gram_fderiv N
  rw [hF]
  exact (gramHessian n m).hasFDerivAt.fderiv

end Yau.NodeProofs.E02Aux
