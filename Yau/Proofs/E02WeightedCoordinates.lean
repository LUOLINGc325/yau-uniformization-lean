import Yau.Proofs.E02ProductMaps
import Yau.Proofs.E02EqualityOrbit

open Matrix Set
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem weightedColumns_bijective {n m : ℕ} (α : Fin m → ℝ) (hα : ∀ j, 0 < α j) :
    Function.Bijective (weightedColumns (n := n) α) := by
  constructor
  · intro u v huv
    ext j i
    have h := congrArg (fun M : Rect n m => M i j) huv
    have hRoot : (Real.sqrt (α j) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hα j)).ne'
    exact mul_left_cancel₀ hRoot h
  · intro M
    refine ⟨fun j => WithLp.toLp 2 (fun i => (Real.sqrt (α j) : ℂ)⁻¹*M i j),?_⟩
    ext i j
    have hRoot : (Real.sqrt (α j) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hα j)).ne'
    change (Real.sqrt (α j) : ℂ)*((Real.sqrt (α j) : ℂ)⁻¹*M i j) = M i j
    rw [←mul_assoc,mul_inv_cancel₀ hRoot,one_mul]

/-- For the fixed positive weights, the actual columns give one global
linear homeomorphism. No optimizer or eigenbasis is varied. -/
def weightedColumnsEquiv {n m : ℕ} (α : Fin m → ℝ) (hα : ∀ j, 0 < α j) :
    (Fin m → ComplexVector n) ≃L[ℂ] Rect n m :=
  (LinearEquiv.ofBijective (weightedColumnsLinear α) (weightedColumns_bijective α hα)).toContinuousLinearEquiv

theorem weightedColumnsEquiv_apply {n m : ℕ} (α : Fin m → ℝ) (hα : ∀ j, 0 < α j)
    (η : Fin m → ComplexVector n) : weightedColumnsEquiv α hα η = weightedColumns α η := rfl

/-- Compactness covers the ENTIRE fixed Gram/projector equality orbit
in the original list of cotangent variables. -/
theorem isCompact_weighted_equality_orbit {n m : ℕ}
    (α : Fin m → ℝ) (hα : ∀ j, 0 < α j) (A B : Herm n) (P₀ : Herm m) :
    IsCompact {η : Fin m → ComplexVector n |
      weightedColumns α η*(weightedColumns α η)ᴴ = A ∧
        (weightedColumns α η)ᴴ*B*weightedColumns α η = P₀} := by
  exact (weightedColumnsEquiv α hα).toHomeomorph.isCompact_preimage.mpr
    (isCompact_equality_orbit A B P₀)

end Yau.NodeProofs.E02Aux
