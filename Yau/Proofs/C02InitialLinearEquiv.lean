import Yau.Proofs.C02UnitaryRealFrame

/-! The normalized initial real isometry is onto, with its actual explicit
inverse. This gives an initial physical orthonormal basis for radial transport. -/

noncomputable section
open scoped Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalInitialLinearEquiv (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) :
    ComplexVector n ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  refine { toLinearMap := normalInitialLinearMap p U
           invFun := fun w => Real.sqrt (2 : ℝ) • U.symm (realTangentEquiv p w)
           left_inv := ?_
           right_inv := ?_ }
  · intro v
    change Real.sqrt (2 : ℝ) • U.symm (realTangentEquiv p (normalInitialLinearMap p U v)) = v
    rw [normalInitialLinearMap_coordinates, U.symm_apply_apply, smul_smul,
      mul_inv_cancel₀ hs, one_smul]
  · intro w
    apply (realTangentEquiv p).injective
    change realTangentEquiv p (normalInitialLinearMap p U
      (Real.sqrt (2 : ℝ) • U.symm (realTangentEquiv p w))) = realTangentEquiv p w
    rw [normalInitialLinearMap_coordinates, smul_smul, inv_mul_cancel₀ hs,
      one_smul, U.apply_symm_apply]

def normalInitialIsometryEquiv (h : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    letI := underlyingRealTangentNormedAddCommGroup h p
    letI := underlyingRealTangentInnerProductSpace h p
    ComplexVector n ≃ₗᵢ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p := by
  letI := underlyingRealTangentNormedAddCommGroup h p
  letI := underlyingRealTangentInnerProductSpace h p
  exact { toLinearEquiv := normalInitialLinearEquiv p U
          norm_map' := normalInitialLinearMap_norm h p U hU }

end Yau.Blueprint.C02Proof
