import Yau.Proofs.D06WeightedOrthogonality
import Yau.Proofs.D06HardyBoundaryBounds

/-! The original weighted Hardy factors and their actual bounded L² traces. -/

open scoped ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

def hardyPColumns (j : Fin r) : HardySeq r :=
  hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper (hardyConst (EuclideanSpace.single j 1))

def hardyQColumns (j : Fin r) : HardySeq r :=
  hardyInverseFactorOperator L hLp hHerm m hm hLower M hM hUpper (hardyConst (EuclideanSpace.single j 1))

def hardyPTrace : HardyCircle → Matrix (Fin r) (Fin r) ℂ :=
  hardyMatrixTrace (hardyPColumns L hLp hHerm m hm hLower M hM hUpper)

def hardyQTrace : HardyCircle → Matrix (Fin r) (Fin r) ℂ :=
  hardyMatrixTrace (hardyQColumns L hLp hHerm m hm hLower M hM hUpper)

theorem hardyPTrace_bound : ∀ᵐ t ∂hardyCircleMeasure,
    matOpNormR (hardyPTrace L hLp hHerm m hm hLower M hM hUpper t) ≤ (Real.sqrt m)⁻¹ :=
  hardyMatrixTrace_bound _ _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (hardyP_bound L hLp hHerm m hm hLower M hM hUpper)

theorem hardyQTrace_bound : ∀ᵐ t ∂hardyCircleMeasure,
    matOpNormR (hardyQTrace L hLp hHerm m hm hLower M hM hUpper t) ≤ Real.sqrt M :=
  hardyMatrixTrace_bound _ _ (Real.sqrt_nonneg _)
    (hardyQ_bound L hLp hHerm m hm hLower M hM hUpper)

theorem hardyPTrace_memLp (i j : Fin r) :
    MemLp (fun t => hardyPTrace L hLp hHerm m hm hLower M hM hUpper t i j) ⊤ hardyCircleMeasure :=
  hardyMatrixTrace_memLp_top _ _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (hardyP_bound L hLp hHerm m hm hLower M hM hUpper) i j

theorem hardyQTrace_memLp (i j : Fin r) :
    MemLp (fun t => hardyQTrace L hLp hHerm m hm hLower M hM hUpper t i j) ⊤ hardyCircleMeasure :=
  hardyMatrixTrace_memLp_top _ _ (Real.sqrt_nonneg _)
    (hardyQ_bound L hLp hHerm m hm hLower M hM hUpper) i j

theorem hardyPTrace_inverse : ∀ᵐ t ∂hardyCircleMeasure,
    hardyPTrace L hLp hHerm m hm hLower M hM hUpper t *
      hardyQTrace L hLp hHerm m hm hLower M hM hUpper t = 1 ∧
    hardyQTrace L hLp hHerm m hm hLower M hM hUpper t *
      hardyPTrace L hLp hHerm m hm hLower M hM hUpper t = 1 :=
  hardyMatrixTrace_inverse _ _ (fun z hz =>
    ⟨hardyP_mul_Q L hLp hHerm m hm hLower M hM hUpper z hz,
      hardyQ_mul_P L hLp hHerm m hm hLower M hM hUpper z hz⟩)

end Yau.NodeProofs.D06Aux
