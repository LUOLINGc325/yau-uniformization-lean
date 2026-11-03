import Yau.Proofs.C03ChernGaugeFlat

/-! The two exact target norms needed for the uniform curvature ratio. -/

noncomputable section
open scoped Manifold Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem target_norm_eq_source_quadratic
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (h : HermitianField M) (Φ : ComplexVector n → M.Carrier)
    (z : (ComplexEuclideanManifold n hn).Carrier)
    (heq : ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (h (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v)) (a : ComplexVector n) :
    hermitianNormSq (h (Φ z)) (mfderiv (ComplexModel n) (ComplexModel n) Φ z a) =
      ellipsoidQuadratic (gMat k z) a := by
  rw [flat_norm_quadratic hn]
  exact congrArg Complex.re (heq a a).symm

theorem target_raised_norm_eq_dual
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (h : HermitianField M) (Φ : ComplexVector n → M.Carrier)
    (z : (ComplexEuclideanManifold n hn).Carrier)
    (heq : ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (h (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v)) (ξ : ComplexVector n) :
    hermitianNormSq (h (Φ z))
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z
          (WithLp.toLp 2 (star (WithLp.ofLp (matrixFiberMap (gMat k z)⁻¹ᵀ ξ))))) =
      dualNormMat (gMat k z) ξ := by
  rw [target_norm_eq_source_quadratic hn k h Φ z heq]
  rw [flat_norm_quadratic hn]
  exact flat_raised_norm hn k z ξ

end Yau.Proofs.C03Aux.ChernGauge
