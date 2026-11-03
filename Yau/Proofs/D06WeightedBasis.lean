import Yau.Proofs.D06WeightedCoefficients
import Yau.Proofs.D06WeightedHilbert
import Yau.Proofs.D06WanderingBasis

/-! The actual weighted Hardy wandering basis, with the original Fin r index. -/

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

theorem weightedShiftLI_pure :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    (⨅ k : ℕ, (weightedShiftLI L hLp hHerm m hm hLower ^ k).range) = ⊥ := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  let S := weightedShiftLI L hLp hHerm m hm hLower
  have hpow : ∀ k : ℕ, (S ^ k).toLinearMap = weightedShiftLinear ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [pow_succ', pow_succ']
        apply LinearMap.ext
        intro a
        change weightedShiftLinear ((S ^ k).toLinearMap a) =
          weightedShiftLinear ((weightedShiftLinear ^ k) a)
        exact congrArg weightedShiftLinear (LinearMap.congr_fun ih a)
  have hrange (k : ℕ) : (S ^ k).range = (weightedShiftLinear ^ k).range :=
    congrArg LinearMap.range (hpow k)
  change (⨅ k : ℕ, (S ^ k).range) = ⊥
  simp_rw [hrange]
  exact weightedShiftLinear_pure

theorem weightedShiftLI_coeff_ker :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    weightedCoeffZeroLM.ker = (weightedShiftLI L hLp hHerm m hm hLower).range := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  change weightedCoeffZeroLM.ker = (weightedShiftLinear (r := r)).range
  exact weightedCoeffZeroLM_ker

def weightedHardyBasis (M : ℝ) (hM : 0 ≤ M)
    (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef) :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    letI : InnerProductSpace ℂ (WeightedHardySeq r) :=
      weightedHardyInnerProduct L hLp hHerm m hm hLower
    HilbertBasis (ℕ × Fin r) ℂ (WeightedHardySeq r) := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  letI : InnerProductSpace ℂ (WeightedHardySeq r) :=
    weightedHardyInnerProduct L hLp hHerm m hm hLower
  letI : CompleteSpace (WeightedHardySeq r) :=
    weightedHardyComplete L hLp hHerm m hm hLower M hM hUpper
  exact pureShiftBasisFromQuotient (weightedShiftLI L hLp hHerm m hm hLower) weightedCoeffZeroLM
    (weightedShiftLI_coeff_ker L hLp hHerm m hm hLower) weightedCoeffZeroLM_surjective
    (weightedShiftLI_pure L hLp hHerm m hm hLower)

def weightedSynthesis (M : ℝ) (hM : 0 ≤ M)
    (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef) :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    HardySeq r ≃ₗᵢ[ℂ] WeightedHardySeq r :=
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  letI : InnerProductSpace ℂ (WeightedHardySeq r) :=
    weightedHardyInnerProduct L hLp hHerm m hm hLower
  (weightedHardyBasis L hLp hHerm m hm hLower M hM hUpper).repr.symm

end Yau.NodeProofs.D06Aux
