import Yau.Proofs.V04WallErrorNormHessian
import Yau.Proofs.V04WallErrorKahlerContraction
import Yau.Proofs.V04WallErrorQuadraticContraction
import Yau.Proofs.V04WallErrorPhysicalTime

/-! The symplectic Hessian of the actual dual norm equals its physical
Kähler–Ricci time derivative, on the closed physical time domain. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.G01Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem symplecticP_normChartHessian
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {p : CotangentCoord n} (hp : p.1 ∈ chartTarget x) :
    symplecticP (normChartHessian h x p) =
      (star (WithLp.ofLp p.2) ⬝ᵥ
        (((hMat h x p.1)⁻¹ * (-leviC (logDet h x) p.1) * (hMat h x p.1)⁻¹)ᵀ *ᵥ
          WithLp.ofLp p.2)).re := by
  have hc := symplecticP_quadratic_contraction (normChartHessian h x p)
    (WithLp.ofLp p.2) (hMat h x p.1)⁻¹
    (mixedMatrixWirt (fun w => (hMat h x w)⁻¹) p.1)
    (matrixWirtBar (fun w => (hMat h x w)⁻¹) p.1)
    (matrixWirt (fun w => (hMat h x w)⁻¹) p.1)
    (fun i j => normChartHessian_horizontal h hs x hp i j)
    (fun i j => normChartHessian_vertical h hs x hp i j)
    (fun i j => normChartHessian_mixed h hs x hp i j)
    (matrixWirtBar_inverse_star h x p.1)
  simp_rw [kahler_contracted_inverse_hessian h hs hk x hp] at hc
  simpa only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.star_apply,
    Finset.mul_sum, mul_assoc] using hc

theorem symplecticP_dualNorm {X : KahlerManifold n}
    (h : HermitianField X.manifold) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (y : CotangentPoint X.manifold) :
    symplecticP (spatialHessian (fun y' => dualNorm h y'.1 y'.2) y) =
      (star (WithLp.ofLp (covectorCoords y.1 y.1 y.2)) ⬝ᵥ
        (((gMat h y.1)⁻¹ * ricci h y.1 * (gMat h y.1)⁻¹)ᵀ *ᵥ
          WithLp.ofLp (covectorCoords y.1 y.1 y.2))).re := by
  rw [spatialHessian_dualNorm_eq_normChartHessian]
  exact symplecticP_normChartHessian h hs hk y.1
    (mem_extChartAt_target y.1)

theorem krf_symplecticP_dualNorm {X : KahlerManifold n}
    {g : HermitianField X.manifold} {h : ℝ → HermitianField X.manifold}
    (hh : IsKahlerRicciFlow g h) {t : ℝ} (ht : 0 ≤ t)
    (y : CotangentPoint X.manifold) :
    symplecticP (spatialHessian (fun y' => dualNorm (h t) y'.1 y'.2) y) =
      derivWithin (fun τ => dualNorm (h τ) y.1 y.2) (Set.Ici 0) t := by
  rw [krf_dualNorm_derivWithin hh y.1 y.2 ht]
  exact symplecticP_dualNorm (h t)
    (metricFamilySmooth_slice hh.2.1 ht) (hh.2.2.1 t ht) y

end Yau.Blueprint.V04Proof.WallErrorAux
