import Yau.Proofs.C02RadialDifferentialIdentity
import Yau.Proofs.C02NormalTorsion
import Yau.Proofs.C02ConnectionRadialZero
import Yau.Proofs.C02NormalDifferentialRadial

/-! Both radial homotopy identities for the actual Exp/parallel gauge.
The curvature here is the computed derivative/commutator of its actual
connection; identification with the transported Riemann tensor is separate. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

def normalConnectionCurvature (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  connectionCurvature (normalConnection g p U hU) x

theorem normalConnection_homotopy (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    normalConnection g p U hU x = radialHomotopy (normalConnectionCurvature g p U hU) x := by
  exact (radial_connection_homotopy (normalConnection g p U hU) (normalConnection_smooth g p U hU)
    (normalConnection_radial_zero g p U hU) x).symm

theorem normalDifferential_homotopy (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    normalDifferential g p U hU x = ContinuousLinearMap.id ℝ (ComplexVector n) +
      radialHomotopy (fun y => (normalConnection g p U hU y).flip) x := by
  exact radial_differential_homotopy (normalConnection g p U hU) (normalDifferential g p U hU)
    (normalConnection_smooth g p U hU) (normalDifferential_smooth g p U hU)
    (normalConnection_radial_zero g p U hU) (normalDifferential_radial g p U hU)
    (normalConnection_torsion g p U hU) x

end Yau.Blueprint.C02Proof
