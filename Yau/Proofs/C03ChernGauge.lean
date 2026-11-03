import Yau.Proofs.C03ChernGaugeBisectional
import Yau.Proofs.C03ChernGaugeResidual
import Yau.Proofs.C03ChernGaugeNorms

/-! The exact computed dual-Chern residual and both unnormalized target
norms, from only the original local Hermitian pullback data. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem computedResidual_pullback
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn)) (ks : MetricSmooth k)
    (h : HermitianField M) (hs : MetricSmooth h)
    {O : Set (ComplexVector n)} (hO : IsOpen O) {Φ : ComplexVector n → M.Carrier}
    (hΦ : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O)
    (hbij : ∀ z ∈ O, Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) Φ z))
    (heq : ∀ (z : (ComplexEuclideanManifold n hn).Carrier), z ∈ O →
      ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (h (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v))
    {z : (ComplexEuclideanManifold n hn).Carrier} (hz : z ∈ O) (ξ a : ComplexVector n) :
    computedResidual (fun w => gMat k w) z ξ a =
      bisectionalForm h (Φ z)
        (tangentCoords (Φ z) (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z
          (WithLp.toLp 2 (star (WithLp.ofLp (matrixFiberMap (gMat k z)⁻¹ᵀ ξ))))))
        (tangentCoords (Φ z) (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z a)) := by
  rw [source_residual_eq_bisectional hn k ks]
  exact bisectionalForm_pullback hn k ks h hs hO hΦ hbij heq hz _ a

end Yau.Proofs.C03Aux.ChernGauge
