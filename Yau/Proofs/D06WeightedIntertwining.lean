import Yau.Proofs.D06WeightedOperators
import Yau.Proofs.D06ShiftSynthesis

/-! The original two bounded Hardy operators commute with the unilateral shift. -/

open scoped ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

theorem weightedSynthesis_intertwines :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    (weightedShiftLI L hLp hHerm m hm hLower).toContinuousLinearMap.comp
      (weightedSynthesis L hLp hHerm m hm hLower M hM hUpper).toLinearIsometry.toContinuousLinearMap =
    (weightedSynthesis L hLp hHerm m hm hLower M hM hUpper).toLinearIsometry.toContinuousLinearMap.comp
      (hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r).toContinuousLinearMap := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  letI : InnerProductSpace ℂ (WeightedHardySeq r) :=
    weightedHardyInnerProduct L hLp hHerm m hm hLower
  letI : CompleteSpace (WeightedHardySeq r) :=
    weightedHardyComplete L hLp hHerm m hm hLower M hM hUpper
  exact pureShiftSynthesis_intertwines (weightedShiftLI L hLp hHerm m hm hLower)
    (wanderingOrthonormalBasis (weightedShiftLI L hLp hHerm m hm hLower) weightedCoeffZeroLM
      (weightedShiftLI_coeff_ker L hLp hHerm m hm hLower) weightedCoeffZeroLM_surjective)
    (weightedShiftLI_pure L hLp hHerm m hm hLower)

theorem hardyFactorOperator_shift (a : HardySeq r) :
    hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper (hardyShift a) =
      hardyShift (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper a) := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  have h := DFunLike.congr_fun
    (weightedSynthesis_intertwines L hLp hHerm m hm hLower M hM hUpper) a
  change weightedUnwrap ((weightedSynthesis L hLp hHerm m hm hLower M hM hUpper) (hardyShift a)) =
    hardyShift (weightedUnwrap ((weightedSynthesis L hLp hHerm m hm hLower M hM hUpper) a))
  exact congrArg weightedUnwrap h.symm

theorem hardyInverseFactorOperator_shift (a : HardySeq r) :
    hardyInverseFactorOperator L hLp hHerm m hm hLower M hM hUpper (hardyShift a) =
      hardyShift (hardyInverseFactorOperator L hLp hHerm m hm hLower M hM hUpper a) := by
  let T := hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper
  let R := hardyInverseFactorOperator L hLp hHerm m hm hLower M hM hUpper
  have hRT (b : HardySeq r) : R (T b) = b :=
    DFunLike.congr_fun (hardyInverseFactorOperator_inverse L hLp hHerm m hm hLower M hM hUpper) b
  have hTR (b : HardySeq r) : T (R b) = b :=
    DFunLike.congr_fun (hardyFactorOperator_inverse L hLp hHerm m hm hLower M hM hUpper) b
  change R (hardyShift a) = hardyShift (R a)
  calc
    R (hardyShift a) = R (hardyShift (T (R a))) := by rw [hTR]
    _ = R (T (hardyShift (R a))) := by
      rw [hardyFactorOperator_shift L hLp hHerm m hm hLower M hM hUpper]
    _ = hardyShift (R a) := hRT _

end Yau.NodeProofs.D06Aux
