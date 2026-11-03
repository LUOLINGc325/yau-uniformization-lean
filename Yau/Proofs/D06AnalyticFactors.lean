import Yau.Proofs.D06WeightedIntertwining
import Yau.Proofs.D06HardySymbolBounds

/-! The original two holomorphic factors synthesized from the weighted Hardy
wandering basis. The inverse is produced from the inverse synthesis operator. -/

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

def hardyP : ℂ → Matrix (Fin r) (Fin r) ℂ :=
  hardySymbol (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper)

def hardyQ : ℂ → Matrix (Fin r) (Fin r) ℂ :=
  hardySymbol (hardyInverseFactorOperator L hLp hHerm m hm hLower M hM hUpper)

theorem hardyP_differentiableOn (i j : Fin r) :
    DifferentiableOn ℂ (fun z => hardyP L hLp hHerm m hm hLower M hM hUpper z i j)
      (Metric.ball 0 1) := hardySymbol_differentiableOn _ i j

theorem hardyQ_differentiableOn (i j : Fin r) :
    DifferentiableOn ℂ (fun z => hardyQ L hLp hHerm m hm hLower M hM hUpper z i j)
      (Metric.ball 0 1) := hardySymbol_differentiableOn _ i j

theorem hardyP_bound (z : ℂ) (hz : ‖z‖ < 1) :
    matOpNormR (hardyP L hLp hHerm m hm hLower M hM hUpper z) ≤ (Real.sqrt m)⁻¹ :=
  hardySymbol_bound _ (hardyFactorOperator_shift L hLp hHerm m hm hLower M hM hUpper)
    _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (hardyFactorOperator_bound L hLp hHerm m hm hLower M hM hUpper) z hz

theorem hardyQ_bound (z : ℂ) (hz : ‖z‖ < 1) :
    matOpNormR (hardyQ L hLp hHerm m hm hLower M hM hUpper z) ≤ Real.sqrt M :=
  hardySymbol_bound _ (hardyInverseFactorOperator_shift L hLp hHerm m hm hLower M hM hUpper)
    _ (Real.sqrt_nonneg _)
    (hardyInverseFactorOperator_bound L hLp hHerm m hm hLower M hM hUpper) z hz

theorem hardyP_mul_Q (z : ℂ) (hz : ‖z‖ < 1) :
    hardyP L hLp hHerm m hm hLower M hM hUpper z *
      hardyQ L hLp hHerm m hm hLower M hM hUpper z = 1 := by
  rw [hardyP, hardyQ, ← hardySymbol_comp _ _
    (hardyFactorOperator_shift L hLp hHerm m hm hLower M hM hUpper) z hz,
    hardyFactorOperator_inverse, hardySymbol_id]

theorem hardyQ_mul_P (z : ℂ) (hz : ‖z‖ < 1) :
    hardyQ L hLp hHerm m hm hLower M hM hUpper z *
      hardyP L hLp hHerm m hm hLower M hM hUpper z = 1 := by
  rw [hardyP, hardyQ, ← hardySymbol_comp _ _
    (hardyInverseFactorOperator_shift L hLp hHerm m hm hLower M hM hUpper) z hz,
    hardyInverseFactorOperator_inverse, hardySymbol_id]

end Yau.NodeProofs.D06Aux
