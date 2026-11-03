import Yau.Proofs.C02RealComplexDifferential
import spec.CHAIN.CONTRACTS
import Yau.Proofs.C02ComplexCoordinateDifferential

/-! Recovering the actual Hermitian pullback coefficients from its physical
real pullback metric. Both use the same genuine manifold differential. -/

noncomputable section
open scoped Manifold
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def realPullbackMetric (h : HermitianField M) (Φ : ComplexVector n → M.Carrier)
    (z u v : ComplexVector n) : ℝ :=
  (underlyingRealRiemannianMetric h).inner (Φ z)
    (realCoordinateDifferential Φ z u) (realCoordinateDifferential Φ z v)

theorem realPullbackMetric_eq_two_re (h : HermitianField M)
    {Φ : ComplexVector n → M.Carrier} {z : ComplexVector n}
    (hΦ : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z)
    (u v : ComplexVector n) :
    realPullbackMetric h Φ z u v = 2 * ((h (Φ z)).toFun
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z u)
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z v)).re := by
  change 2 * ((h (Φ z)).toFun
    (realTangentEquiv (Φ z) (realCoordinateDifferential Φ z u))
    (realTangentEquiv (Φ z) (realCoordinateDifferential Φ z v))).re = _
  rw [realCoordinateDifferential_eq_complex hΦ u, realCoordinateDifferential_eq_complex hΦ v]

theorem pullbackMat_eq_real_metric_coefficients (h : HermitianField M)
    {Φ : ComplexVector n → M.Carrier} {z : ComplexVector n}
    (hΦ : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z) (a b : Fin n) :
    pullbackMat h Φ z a b =
      ((1 / 2 : ℝ) * realPullbackMetric h Φ z (stdVec a) (stdVec b) : ℂ) +
        Complex.I * ((1 / 2 : ℝ) * realPullbackMetric h Φ z (Complex.I • stdVec a) (stdVec b) : ℂ) := by
  let D := complexCoordinateDifferential Φ z
  have hG (u v : ComplexVector n) : realPullbackMetric h Φ z u v =
      2 * ((h (Φ z)).toFun (D u) (D v)).re := realPullbackMetric_eq_two_re h hΦ u v
  change (h (Φ z)).toFun (D (stdVec a)) (D (stdVec b)) = _
  rw [hG, hG, D.map_smul Complex.I (stdVec a), HermitianInnerProduct.map_smul_left]
  apply Complex.ext <;>
    simp [pullbackMat, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]

end Yau.Blueprint.C02Proof
