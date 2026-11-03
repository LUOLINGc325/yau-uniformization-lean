import Yau.Proofs.D06WeightedBasis

/-! Ordinary bounded inverse operators synthesized from the actual weighted
wandering basis. These will produce the original two Hardy matrix factors. -/

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

def hardyFactorOperator : HardySeq r →L[ℂ] HardySeq r :=
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  (weightedUnwrapCLM L hLp hHerm m hm hLower).comp
    (weightedSynthesis L hLp hHerm m hm hLower M hM hUpper).toLinearIsometry.toContinuousLinearMap

def hardyInverseFactorOperator : HardySeq r →L[ℂ] HardySeq r :=
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  (weightedSynthesis L hLp hHerm m hm hLower M hM hUpper).symm.toLinearIsometry.toContinuousLinearMap.comp
    (weightedWrapCLM L hLp hHerm m hm hLower M hM hUpper)

theorem hardyFactorOperator_bound (a : HardySeq r) :
    ‖hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper a‖ ≤ (Real.sqrt m)⁻¹ * ‖a‖ := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  let U := weightedSynthesis L hLp hHerm m hm hLower M hM hUpper
  change ‖weightedUnwrap (U a)‖ ≤ (Real.sqrt m)⁻¹ * ‖a‖
  have h := weighted_unwrap_norm_le L hLp hHerm m hm hLower (U a)
  simpa only [LinearIsometryEquiv.norm_map] using h

theorem hardyInverseFactorOperator_bound (a : HardySeq r) :
    ‖hardyInverseFactorOperator L hLp hHerm m hm hLower M hM hUpper a‖ ≤ Real.sqrt M * ‖a‖ := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  let U := weightedSynthesis L hLp hHerm m hm hLower M hM hUpper
  change ‖U.symm (weightedUnwrap.symm a)‖ ≤ Real.sqrt M * ‖a‖
  rw [LinearIsometryEquiv.norm_map]
  exact weighted_wrap_norm_le L hLp hHerm m hm hLower M hM hUpper a

theorem hardyFactorOperator_inverse :
    (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper).comp
      (hardyInverseFactorOperator L hLp hHerm m hm hLower M hM hUpper) =
        ContinuousLinearMap.id ℂ (HardySeq r) := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  let U := weightedSynthesis L hLp hHerm m hm hLower M hM hUpper
  apply ContinuousLinearMap.ext
  intro a
  change weightedUnwrap (U (U.symm (weightedUnwrap.symm a))) = a
  rw [U.apply_symm_apply, weightedUnwrap.apply_symm_apply]

theorem hardyInverseFactorOperator_inverse :
    (hardyInverseFactorOperator L hLp hHerm m hm hLower M hM hUpper).comp
      (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper) =
        ContinuousLinearMap.id ℂ (HardySeq r) := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  let U := weightedSynthesis L hLp hHerm m hm hLower M hM hUpper
  apply ContinuousLinearMap.ext
  intro a
  change U.symm (weightedUnwrap.symm (weightedUnwrap (U a))) = a
  rw [weightedUnwrap.symm_apply_apply, U.symm_apply_apply]

end Yau.NodeProofs.D06Aux
