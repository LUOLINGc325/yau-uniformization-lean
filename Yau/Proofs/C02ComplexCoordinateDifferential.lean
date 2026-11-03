import Yau.LeafProofs.L12

/-! The canonical source tangent identification makes the actual complex
manifold differential a linear map on the coordinate vector space. -/

noncomputable section
open scoped Manifold
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

def complexCoordinateDifferential (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℂ] TangentVector M (Φ z) :=
  (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z).comp
    (NormedSpace.fromTangentSpace (𝕜 := ℂ) z).symm.toContinuousLinearMap

theorem complexCoordinateDifferential_apply (Φ : ComplexVector n → M.Carrier)
    (z u : ComplexVector n) : complexCoordinateDifferential Φ z u =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z u := rfl

end Yau.Blueprint.C02Proof
