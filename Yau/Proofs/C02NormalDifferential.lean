import Yau.Proofs.C02ParallelGaugeFrame
import Yau.Proofs.C02OperatorSmoothInverse

/-! The normal-gauge matrix is the actual real manifold differential expressed
in the genuine parallel isometry. It is defined before any nonsingularity claim. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def rawNormalDifferential (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (x : ComplexVector n) :
    ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (normalRealMap g p U x) := by
  letI := manifold_realSmooth M
  exact (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) (normalRealMap g p U) x).comp
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.toContinuousLinearMap

def normalDifferential (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact (normalParallelIsometry g p U hU x).symm.toContinuousLinearMap.comp
    (rawNormalDifferential g p U x)

theorem normalDifferential_reconstruct (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x z : ComplexVector n) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    normalParallelIsometry g p U hU x (normalDifferential g p U hU x z) =
      rawNormalDifferential g p U x z := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact (normalParallelIsometry g p U hU x).apply_symm_apply _

theorem rawNormalDifferential_bijective_of_close_identity
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n)
    (hClose : ‖normalDifferential g p U hU x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4) :
    Function.Bijective (rawNormalDifferential g p U x) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hB := (isInvertible_of_close_identity _ hClose).bijective
  have heq : (fun z => normalParallelIsometry g p U hU x (normalDifferential g p U hU x z)) =
      rawNormalDifferential g p U x := funext (normalDifferential_reconstruct g p U hU x)
  rw [← heq]
  exact (normalParallelIsometry g p U hU x).bijective.comp hB

end Yau.Blueprint.C02Proof
