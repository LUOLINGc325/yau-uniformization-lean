import Yau.LeafProofs.L12

/-! The real coordinate differential and complex manifold differential
are the same actual tangent vector under the canonical identification. -/

noncomputable section
open scoped Manifold
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def realCoordinateDifferential (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (Φ z) := by
  letI := manifold_realSmooth M
  exact (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) Φ z).comp
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap

theorem realCoordinateDifferential_eq_complex
    {Φ : ComplexVector n → M.Carrier} {z : ComplexVector n}
    (hΦ : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z)
    (u : ComplexVector n) :
    realTangentEquiv (Φ z) (realCoordinateDifferential Φ z u) =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z u := by
  let S := ComplexEuclideanManifold n (Nat.succ_le_iff.mpr (manifold_dimension_pos M))
  have hf : MDifferentiableAt (ComplexModel n) (ComplexModel n)
      (fun x : S.Carrier => Φ x) z := hΦ
  have hd := mfderiv_real (M := S) (N := M) hf
  have hs : realTangentEquiv (M := S) z
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u) = u := rfl
  have hv := congrArg (fun A => realTangentEquiv (Φ z)
    (A ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u))) hd
  change realTangentEquiv (Φ z) (realCoordinateDifferential Φ z u) =
    realTangentEquiv (Φ z) ((realTangentEquiv (Φ z)).symm
      (((mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z).restrictScalars ℝ)
        (realTangentEquiv (M := S) z
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u)))) at hv
  rw [ContinuousLinearEquiv.apply_symm_apply, hs] at hv
  exact hv

end Yau.Blueprint.C02Proof
