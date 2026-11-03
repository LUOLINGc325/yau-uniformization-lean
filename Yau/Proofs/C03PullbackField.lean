import Yau.Proofs.C03HermitianProducts
import Yau.Geometry.Flat
import Yau.Blueprint.Nodes

/-! A globally positive Hermitian field agreeing with the actual pullback
where the cutoff is one. No global invertibility of the chart is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint

variable {n : ℕ}

def localPullbackProduct (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (z : (ComplexEuclideanManifold n hn).Carrier)
    (hz : z ∈ Metric.ball (0 : ComplexVector n) r) :
    HermitianInnerProduct (TangentVector (ComplexEuclideanManifold n hn) z) :=
  pullbackHermitian (X.metric.form (Φ z))
    (mfderiv (ComplexModel n) (ComplexModel n) Φ z).toLinearMap
    (hΦ.2 z hz).injective

def cutoffPullbackField (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) :
    HermitianField (ComplexEuclideanManifold n hn) := by
  classical
  exact fun z => if hz : z ∈ Metric.ball (0 : ComplexVector n) r then
    blendHermitian (localPullbackProduct hn X Φ r hΦ z hz) (flatHermitianField hn z)
      (χ z) (hχ z).1 (hχ z).2
    else flatHermitianField hn z

theorem cutoffPullbackField_of_mem (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (z : (ComplexEuclideanManifold n hn).Carrier)
    (hz : z ∈ Metric.ball (0 : ComplexVector n) r)
    (u v : TangentVector (ComplexEuclideanManifold n hn) z) :
    (cutoffPullbackField hn X Φ r hΦ χ hχ z).toFun u v =
      (χ z : ℂ) * (X.metric.form (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v) +
      ((1 - χ z : ℝ) : ℂ) * (flatHermitianField hn z).toFun u v := by
  simp only [cutoffPullbackField, dif_pos hz, blendHermitian,
    localPullbackProduct, pullbackHermitian, ContinuousLinearMap.coe_coe]

theorem cutoffPullbackField_eq_pullback_of_one (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (z : (ComplexEuclideanManifold n hn).Carrier)
    (hz : z ∈ Metric.ball (0 : ComplexVector n) r)
    (hone : χ z = 1) (u v : TangentVector (ComplexEuclideanManifold n hn) z) :
    (cutoffPullbackField hn X Φ r hΦ χ hχ z).toFun u v =
      (X.metric.form (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v) := by
  rw [cutoffPullbackField_of_mem hn X Φ r hΦ χ hχ z hz]
  simp only [hone, Complex.ofReal_one, one_mul, sub_self, Complex.ofReal_zero,
    zero_mul, add_zero]

theorem cutoffPullbackField_eq_flat_of_zero (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (z : (ComplexEuclideanManifold n hn).Carrier) (hzero : χ z = 0)
    (u v : TangentVector (ComplexEuclideanManifold n hn) z) :
    (cutoffPullbackField hn X Φ r hΦ χ hχ z).toFun u v =
      (flatHermitianField hn z).toFun u v := by
  classical
  by_cases hz : z ∈ Metric.ball (0 : ComplexVector n) r
  · rw [cutoffPullbackField_of_mem hn X Φ r hΦ χ hχ z hz]
    simp only [hzero, Complex.ofReal_zero, zero_mul, sub_zero, Complex.ofReal_one,
      one_mul, zero_add]
  · simp only [cutoffPullbackField, dif_neg hz]

end Yau.Proofs.C03Aux
