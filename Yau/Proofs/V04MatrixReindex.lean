import Yau.Blueprint.VariationContracts
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.CStarAlgebra.Basic

/-! Relabel matrices by a genuine finite index equivalence. The actual
Euclidean operator norm, PSD order, and original Fourier seminorm are
preserved, including empty index types. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def matrixReindexStarAlgEquiv (e : I ≃ J) : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e
  map_smul' c A := by apply Matrix.ext; intro i j; rfl
  map_star' A := by apply Matrix.ext; intro i j; rfl

theorem matrixReindexStarAlgEquiv_apply (e : I ≃ J) (A : Matrix I I ℂ) (i j : J) :
    matrixReindexStarAlgEquiv e A i j = A (e.symm i) (e.symm j) := rfl

theorem matrixReindex_rectOpNorm (e : I ≃ J) (A : Matrix I I ℂ) :
    rectOpNorm (matrixReindexStarAlgEquiv e A) = rectOpNorm A := by
  change ‖matrixReindexStarAlgEquiv e A‖ = ‖A‖
  exact StarAlgEquiv.norm_map _ _

theorem matrixReindex_posSemidef (e : I ≃ J) {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (matrixReindexStarAlgEquiv e A).PosSemidef := by
  change (A.submatrix e.symm e.symm).PosSemidef
  exact hA.submatrix e.symm

theorem matrixDSq_reindex (e : I ≃ J) (A : ℝ → Matrix I I ℂ) :
    matrixDSq (fun θ => matrixReindexStarAlgEquiv e (A θ)) = matrixDSq A := by
  unfold matrixDSq boundaryDSq
  exact (e.symm.prodCongr e.symm).sum_comp (fun p : I × I =>
    ∑' k : ℤ, ENNReal.ofReal (|k| * ‖circleFourier (fun θ => A θ p.1 p.2) k‖ ^ 2))

def cotangentFinEquiv (n : ℕ) : CotangentIndex n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (by omega : n + n = 2 * n))

end Yau.Blueprint.V04Proof
