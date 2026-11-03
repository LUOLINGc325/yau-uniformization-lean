import Yau.Proofs.C02ParallelRescale
import Yau.Proofs.C02ParallelCoefficients

/-! The radial gauge at a rescaled input is exactly the original parallel
flow at the rescaled physical time, including all negative and zero times. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalParallelTotalSpace_radial (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x z : ComplexVector n) (t : ℝ) :
    normalParallelTotalSpace g p U hU (t • x, z) =
      realTransportVector (realParallelTransportFlow g
        (⟨p, (normalInitialLinearMap p U x, normalInitialLinearMap p U z)⟩ : realTransportBundle M) t) := by
  rw [normalParallelTotalSpace_eq_endpointVector]
  have h := parallelTransportFlow_rescale g t
    (⟨p, (normalInitialLinearMap p U x, normalInitialLinearMap p U z)⟩ : realTransportBundle M) 1
  have hi : (⟨p, (normalInitialLinearMap p U (t • x), normalInitialLinearMap p U z)⟩ :
      realTransportBundle M) = transportVelocityScale t
        ⟨p, (normalInitialLinearMap p U x, normalInitialLinearMap p U z)⟩ := by
    simp only [transportVelocityScale, map_smul]
  rw [hi, h, one_mul]
  rfl

theorem normalParallelCoefficients_radial (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x z : ComplexVector n) (t : ℝ) :
    normalParallelCoefficients g p U hU c (t • x) z =
      realTangentCoords c
        (realGeodesicFlow g (⟨p, normalInitialLinearMap p U x⟩ :
          TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t).proj
        (realParallelField g ⟨p, normalInitialLinearMap p U x⟩
          (normalInitialLinearMap p U z) t) := by
  have h := normalParallelTotalSpace_radial g p U hU x z t
  have hp := realParallelField_totalSpace g ⟨p, normalInitialLinearMap p U x⟩
    (normalInitialLinearMap p U z) t
  have heq : normalParallelTotalSpace g p U hU (t • x, z) =
      (⟨(realGeodesicFlow g (⟨p, normalInitialLinearMap p U x⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t).proj,
          realParallelField g ⟨p, normalInitialLinearMap p U x⟩ (normalInitialLinearMap p U z) t⟩ :
            TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := h.trans hp.symm
  exact congrArg (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
    (realPhaseChart c q).2) heq

end Yau.Blueprint.C02Proof
