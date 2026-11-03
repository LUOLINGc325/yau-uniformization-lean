import Yau.Proofs.C02UnitaryFrame
import Yau.LeafProofs.L12

/-! The initial real isometry uses U/sqrt(2), because the original physical
Riemannian metric is 2 Re h. No metric or geodesic clock is rescaled. -/

noncomputable section
open scoped Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalInitialLinearMap (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) :
    ComplexVector n →ₗ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p :=
  (realTangentEquiv p).symm.toLinearEquiv.toLinearMap.comp
    ((U.restrictScalars ℝ).toLinearMap.comp
      ((Real.sqrt (2 : ℝ))⁻¹ • (LinearMap.id : ComplexVector n →ₗ[ℝ] ComplexVector n)))

theorem normalInitialLinearMap_coordinates (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (v : ComplexVector n) :
    realTangentEquiv p (normalInitialLinearMap p U v) =
      U ((Real.sqrt (2 : ℝ))⁻¹ • v) :=
  (realTangentEquiv p).apply_symm_apply _

theorem normalInitialLinearMap_norm (h : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (v : ComplexVector n) :
    letI := underlyingRealTangentNormedAddCommGroup h p
    ‖normalInitialLinearMap p U v‖ = ‖v‖ := by
  letI := underlyingRealTangentNormedAddCommGroup h p
  rw [underlyingRealTangent_norm, normalInitialLinearMap_coordinates,
    unitaryTangentFrame_normSq h p U hU]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hr : 2 * (Real.sqrt (2 : ℝ))⁻¹ ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have heq : 2 * ((Real.sqrt (2 : ℝ))⁻¹ * ‖v‖) ^ 2 = ‖v‖ ^ 2 := by
    calc
      _ = (2 * (Real.sqrt (2 : ℝ))⁻¹ ^ 2) * ‖v‖ ^ 2 := by ring
      _ = _ := by rw [hr, one_mul]
  rw [heq, Real.sqrt_sq (norm_nonneg _)]

def normalInitialIsometry (h : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    letI := underlyingRealTangentNormedAddCommGroup h p
    letI := underlyingRealTangentInnerProductSpace h p
    ComplexVector n →ₗᵢ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p := by
  letI := underlyingRealTangentNormedAddCommGroup h p
  letI := underlyingRealTangentInnerProductSpace h p
  exact { toLinearMap := normalInitialLinearMap p U
          norm_map' := normalInitialLinearMap_norm h p U hU }

end Yau.Blueprint.C02Proof
