import Yau.Proofs.C02NormalDifferentialSmooth

/-! Exact coordinate reconstruction of the genuine normal differential. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalDifferential_coords (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x u : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalParallelCoefficients g p U hU c x (normalDifferential g p U hU x u) =
      fderiv ℝ (normalCoordinateMap g p U c) x u := by
  rw [normalDifferential_eq_coordinates g p U hU c x hx]
  have hRight := (normalParallelCoefficient_inverse_identities g p U hU c x hx).1
  exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n =>
    L (fderiv ℝ (normalCoordinateMap g p U c) x u)) hRight

end Yau.Blueprint.C02Proof
