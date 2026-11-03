import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

open Set Metric
open scoped Topology Matrix.Norms.Frobenius ComplexOrder
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapInverseHolderAux

local instance bootstrapInverseMatrix_topology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)).toUniformSpace.toTopologicalSpace

theorem matrix_inverse_continuousAt_of_isUnit {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) :
    ContinuousAt (fun H : Matrix (Fin n) (Fin n) ℂ => H⁻¹) A := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse, hA.unit_spec] using
    (NormedRing.inverse_continuousAt hA.unit)

theorem matrix_posDef_of_uniform_lower {n : ℕ} {lambda : ℝ} (hlambda : 0 < lambda)
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : (A-(lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef) :
    A.PosDef := by
  have hp : ((lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hlambda)
  simpa only [add_sub_cancel] using hp.add_posSemidef hA

theorem exists_uniform_inverse_norm_bound (n : ℕ) (lambda R : ℝ) (hlambda : 0 < lambda) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ A : Matrix (Fin n) (Fin n) ℂ,
      ‖A‖ ≤ R → (A-(lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef →
      ‖A⁻¹‖ ≤ B := by
  let S : Set (Matrix (Fin n) (Fin n) ℂ) :=
    closedBall 0 R ∩ {A | (A-(lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef}
  have hClosed : IsClosed {A : Matrix (Fin n) (Fin n) ℂ |
      (A-(lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)
  have hS : IsCompact S := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) R).inter_right hClosed
  have hInv : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => ‖A⁻¹‖) S := by
    intro A hA
    exact (matrix_inverse_continuousAt_of_isUnit
      (matrix_posDef_of_uniform_lower hlambda hA.2).isUnit).norm.continuousWithinAt
  obtain ⟨B,hB⟩ := hS.bddAbove_image hInv
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro A hNorm hLower
  apply (hB ?_).trans (le_max_right _ _)
  exact ⟨A,⟨by simpa only [mem_closedBall,dist_zero_right] using hNorm,hLower⟩,rfl⟩

theorem matrix_inverse_difference {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹-B⁻¹=A⁻¹*(B-A)*B⁻¹ :=
  Matrix.inv_sub_inv ⟨fun _ => hB,fun _ => hA⟩

theorem matrix_weighted_inverse_difference_norm_le {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) (hB : IsUnit B)
    (c : ℝ) {C N : ℝ} (hC : 0 ≤ C) (hAinv : ‖A⁻¹‖ ≤ C) (hBinv : ‖B⁻¹‖ ≤ C)
    (hDiff : ‖c • (B-A)‖ ≤ N) : ‖c • (A⁻¹-B⁻¹)‖ ≤ C^2*N := by
  have hN : 0 ≤ N := (norm_nonneg _).trans hDiff
  have hEq : c • (A⁻¹-B⁻¹)=A⁻¹*(c • (B-A))*B⁻¹ := by
    rw [matrix_inverse_difference hA hB,Matrix.mul_smul,Matrix.smul_mul]
  rw [hEq]
  calc
    _ ≤ (‖A⁻¹‖*‖c • (B-A)‖)*‖B⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (C*N)*C := by gcongr
    _ = C^2*N := by ring

end Yau.LeafProofs.L17BootstrapInverseHolderAux
