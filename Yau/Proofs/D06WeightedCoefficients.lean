import Yau.Proofs.D06WeightedShift
import Yau.Proofs.D06HardyCoordinates

/-! The zeroth-coefficient quotient of the actual weighted shift. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def weightedCoeffZeroLM : WeightedHardySeq r →ₗ[ℂ] EuclideanSpace ℂ (Fin r) :=
  hardyCoeffZeroLM.comp weightedUnwrapLM

theorem weightedCoeffZeroLM_surjective : Function.Surjective (weightedCoeffZeroLM (r := r)) := by
  intro v
  refine ⟨weightedUnwrap.symm (hardyConst v), ?_⟩
  change hardyCoeffZero (weightedUnwrap (weightedUnwrap.symm (hardyConst v))) = v
  rw [LinearEquiv.apply_symm_apply, hardyCoeffZero_const]

theorem weightedCoeffZeroLM_ker :
    (weightedCoeffZeroLM (r := r)).ker = weightedShiftLinear.range := by
  ext a
  constructor
  · intro ha
    change hardyCoeffZero (weightedUnwrap a) = 0 at ha
    have h0 : ∀ j, weightedUnwrap a (0, j) = 0 := by
      intro j
      have h := congrArg (fun v : EuclideanSpace ℂ (Fin r) => v j) ha
      exact h
    refine ⟨weightedUnwrap.symm (hardyTail (weightedUnwrap a)), ?_⟩
    apply weightedUnwrap.injective
    rw [weightedShiftLinear_unwrap, LinearEquiv.apply_symm_apply]
    exact hardyShift_tail (weightedUnwrap a) h0
  · rintro ⟨b, rfl⟩
    change hardyCoeffZero (weightedUnwrap (weightedShiftLinear b)) = 0
    rw [weightedShiftLinear_unwrap]
    ext j
    change hardyShift (weightedUnwrap b) (0, j) = 0
    exact hardyShift_zero (weightedUnwrap b) j

end Yau.NodeProofs.D06Aux
