import Yau.Proofs.P03CoefficientCharts
import Yau.LeafProofs.L07

open scoped Manifold Topology ContDiff ComplexOrder Matrix
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

def antiCanonicalCoefficientLinearEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    AntiCanonicalFiber M x ≃ₗ[ℂ] (Fin 1 → ℂ) :=
  (antiCanonicalCoordinateEquiv a x hx).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℂ (Fin 1 → ℂ))

def tangentAntiCanonicalCoefficientLinearEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    TangentAntiCanonicalFiber M x ≃ₗ[ℂ] (Fin n → ℂ) :=
  (tangentAntiCanonicalCoordinateLinearEquiv a x hx).trans
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))

def antiCanonicalCenterMatrix (g : HermitianField M) (x : M.Carrier) :
    Matrix (Fin 1) (Fin 1) ℂ := (gMat g x).det • 1

def tangentAntiCanonicalCenterMatrix (g : HermitianField M) (x : M.Carrier) :
    Matrix (Fin n) (Fin n) ℂ := (gMat g x).det • gMat g x

theorem antiCanonicalCenterMatrix_posDef (g : HermitianField M) (x : M.Carrier) :
    (antiCanonicalCenterMatrix g x).PosDef :=
  (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef).smul (gMat_posDef g x).det_pos

theorem tangentAntiCanonicalCenterMatrix_posDef (g : HermitianField M) (x : M.Carrier) :
    (tangentAntiCanonicalCenterMatrix g x).PosDef :=
  (gMat_posDef g x).smul (gMat_posDef g x).det_pos

/-- The induced line metric is defined on the actual continuous dual-top fibre. -/
def antiCanonicalMetric (g : HermitianField M) : Metric (M := M) (AntiCanonicalFiber M) := fun x =>
  let e := antiCanonicalCoefficientLinearEquiv x x (mem_extChartAt_source x)
  hermitianPullback
    (L14Aux.matrixHermitianMetric (antiCanonicalCenterMatrix g x)
      (antiCanonicalCenterMatrix_posDef g x)) e.toLinearMap e.injective

/-- The induced determinant-tensor metric is defined on the actual tensor fibre. -/
def tangentAntiCanonicalMetric (g : HermitianField M) :
    Metric (M := M) (TangentAntiCanonicalFiber M) :=
  fun x =>
    let e := tangentAntiCanonicalCoefficientLinearEquiv x x (mem_extChartAt_source x)
    hermitianPullback
      (L14Aux.matrixHermitianMetric (tangentAntiCanonicalCenterMatrix g x)
        (tangentAntiCanonicalCenterMatrix_posDef g x)) e.toLinearMap e.injective

theorem antiCanonicalMetric_center_pairing (g : HermitianField M) (x : M.Carrier)
    (u v : AntiCanonicalFiber M x) :
    (antiCanonicalMetric g x).toFun u v =
      star (WithLp.ofLp (antiCanonicalCoordinateEquiv x x (mem_extChartAt_source x) u)) ⬝ᵥ
        (antiCanonicalCenterMatrix g x *ᵥ
          WithLp.ofLp (antiCanonicalCoordinateEquiv x x (mem_extChartAt_source x) v)) := rfl

theorem tangentAntiCanonicalMetric_center_pairing (g : HermitianField M) (x : M.Carrier)
    (u v : TangentAntiCanonicalFiber M x) :
    (tangentAntiCanonicalMetric g x).toFun u v =
      star (WithLp.ofLp (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x) u)) ⬝ᵥ
        (tangentAntiCanonicalCenterMatrix g x *ᵥ
          WithLp.ofLp (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x) v)) := rfl

theorem antiCanonicalMetric_center_apply (g : HermitianField M) (x : M.Carrier)
    (u v : AntiCanonicalFiber M x) :
    (antiCanonicalMetric g x).toFun u v =
      star (u (chartTopForm x x (mem_extChartAt_source x))) * (gMat g x).det *
        v (chartTopForm x x (mem_extChartAt_source x)) := by
  rw [antiCanonicalMetric_center_pairing g x u v]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.star_apply,
    antiCanonicalCenterMatrix, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, one_mul, antiCanonicalCoordinateEquiv_apply, mul_assoc]

end Yau.NodeProofs.P03Aux
