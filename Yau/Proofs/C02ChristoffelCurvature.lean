import Yau.Proofs.C02ConnectionCurvature
import Yau.LeafProofs.L12JacobiCurvature

/-! Identification of the computed connection curvature with the native
Levi--Civita curvature action, before any normal-map invertibility. -/

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chartConnectionCurvature_eq (h : HermitianField M) (c : M.Carrier)
    (y u v w : ComplexVector n) :
    connectionCurvature (chartChristoffelBilin h c) y u v w =
      chartCurvatureVector h c y u v w := by
  rfl

theorem chartConnectionCurvature_component (g : SmoothMetric M) (c : M.Carrier)
    (y : ComplexVector n) (hy : y ∈ chartTarget c) (a b k d : RIdx n) :
    realCoord (connectionCurvature (chartChristoffelBilin g.form c) y
      (realVec a) (realVec b) (realVec k)) d = riemannCoeff g.form c y a b k d := by
  rw [chartConnectionCurvature_eq, chartCurvatureVector_basis g c y hy,
    realCoord_sum_realVec]

end Yau.Blueprint.C02Proof
