import Yau.Proofs.V03RectOperator

/-! The exact rectangular Euclidean operator norm is a continuous function
of the matrix entries. Compact coefficient bounds therefore give actual
uniform operator bounds. -/

open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def matrixEuclideanOperator {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] :
    Matrix ι κ ℂ →L[ℂ] (EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι) := by
  classical
  exact (((LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι) ≃ₗ[ℂ]
        (EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι)).toLinearMap).comp
      Matrix.toEuclideanLin.toLinearMap).toContinuousLinearMap

theorem matrixEuclideanOperator_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) : matrixEuclideanOperator A = (Matrix.toEuclideanLin A).toContinuousLinearMap := by
  classical
  rfl

theorem continuous_rectOpNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Continuous (rectOpNorm : Matrix ι κ ℂ → ℝ) := by
  classical
  have hh := (matrixEuclideanOperator (ι := ι) (κ := κ)).continuous.norm
  change Continuous (fun A : Matrix ι κ ℂ => ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖)
  simpa only [matrixEuclideanOperator_apply] using hh

theorem compact_rectOpNorm_bound {P ι κ : Type*} [TopologicalSpace P]
    [Fintype ι] [Fintype κ] {S : Set P} (hS : IsCompact S) {A : P → Matrix ι κ ℂ}
    (hA : ∀ i j, ContinuousOn (fun p => A p i j) S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, rectOpNorm (A p) ≤ C := by
  have hc : ContinuousOn A S := continuousOn_pi.mpr fun i => continuousOn_pi.mpr (hA i)
  have hn := continuous_rectOpNorm.comp_continuousOn hc
  obtain ⟨C, hC⟩ := (hS.image_of_continuousOn hn).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp
  have hh := hC (rectOpNorm (A p)) ⟨p, hp, rfl⟩
  exact (le_trans (le_abs_self _) hh).trans (le_max_left _ _)

end Yau.Blueprint.V03Proof
