import Yau.Proofs.E02VerticalBlockOrder
import Yau.Proofs.E02WeightedColumnLevi

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem weightedColumns_single {n m : ℕ} (α : Fin m → ℝ) (j : Fin m) (V : ComplexVector n) :
    weightedColumns α (Pi.single j V) = singleColumn j ((Real.sqrt (α j) : ℂ) • V) := by
  ext a b
  by_cases h : b=j
  · subst b
    simp [weightedColumns,singleColumn,Matrix.vecMulVec_apply,smul_eq_mul]
  · simp [weightedColumns,singleColumn,Matrix.vecMulVec_apply,Pi.single_apply,h]

/-- The full same-contact form inequality forces the precise lower
matrix in every vertical block, with its actual inverse Gram matrix. -/
theorem verticalBlock_order_of_contact_forms {n m : ℕ}
    (α : Fin m → ℝ) (η : Fin m → ComplexVector n) (hα : ∀ i, 0 < α i)
    (hM : (weightedColumns α η*(weightedColumns α η)ᴴ).PosDef)
    (W : Fin m → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hW : ∀ i, (W i).IsHermitian) (H : Herm n) (θ : ℝ)
    (hForm : ∀ (X : ComplexVector n) (V : Fin m → ComplexVector n),
      qform H X+(1-θ)*rectLevi logGram (weightedColumns α η) (weightedColumns α V) ≤
        ∑ i, α i*(star (cotangentVector X (V i)) ⬝ᵥ (W i*ᵥcotangentVector X (V i))).re)
    (j : Fin m) :
    ((W j).toBlocks₂₂-
      (((1-θ)*(1-α j*qform ((weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹) (η j)) : ℝ) : ℂ) •
        (weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹).PosSemidef := by
  classical
  apply verticalBlock_order_of_weighted_quadratic (W j) (hW j)
    ((weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹) hM.inv.isHermitian
    (α j) ((1-θ)*(1-α j*qform ((weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹) (η j))) (hα j)
  intro V
  have h := hForm 0 (Pi.single j V)
  have hSum : (∑ i, α i*(star (cotangentVector 0 ((Pi.single j V : Fin m → ComplexVector n) i)) ⬝ᵥ
      (W i*ᵥcotangentVector 0 ((Pi.single j V : Fin m → ComplexVector n) i))).re) =
      α j*(star (cotangentVector 0 V) ⬝ᵥ (W j*ᵥcotangentVector 0 V)).re := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij]
      simp [cotangentVector]
    · simp
  rw [weightedColumns_single,logGram_rectLevi_weightedColumn α η (fun i => (hα i).le) hM j V,
    hSum] at h
  have hZero : qform H (0 : ComplexVector n) = 0 := by simp [qform]
  rw [hZero,zero_add] at h
  convert h using 1 <;> ring

end Yau.NodeProofs.E02Aux
