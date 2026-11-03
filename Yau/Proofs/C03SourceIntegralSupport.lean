import Yau.Proofs.C03SourceIntegral

/-! Natural support and nonnegative-weight bounds supply the full weighted pointwise cap. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Topology Manifold ENNReal Classical
namespace Yau.Proofs.C03Aux.SourceIntegral
open Yau Yau.Proofs.P04Aux BundleDbar
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem inverseCurvatureIntegral_le_support (hn : 1 ≤ n) (R C : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (φ : ComplexVector n → ℝ)
    (f : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 1)
    (S : Set (ComplexVector n)) (hS : S ⊆ closedBall 0 R)
    (hbound : ∀ x ∈ S, inverseCurvatureNormSq (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric φ f x ≤ ENNReal.ofReal C)
    (hφ : ∀ x ∈ S, 0 ≤ φ x)
    (hzero : ∀ x ∉ S, inverseCurvatureNormSq (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric φ f x = 0) :
    inverseCurvatureIntegral (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn) φ f ≤
      ENNReal.ofReal (C * (volume : Measure (ComplexVector n)).real (closedBall 0 R)) := by
  apply inverseCurvatureIntegral_le_ball hn R C hR hC φ f
  intro x
  by_cases hx : x ∈ S
  · rw [if_pos (hS hx)]
    have he : ENNReal.ofReal (Real.exp (-φ x)) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr (hφ x hx))
    simpa only [mul_one] using mul_le_mul' (hbound x hx) he
  · rw [hzero x hx, zero_mul]
    exact bot_le

theorem inverseCurvatureIntegral_le_coefficient_support (hn : 1 ≤ n) (R C : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (φ : ComplexVector n → ℝ)
    (f : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 1)
    (S : Set (ComplexVector n)) (hS : S ⊆ closedBall 0 R)
    (hN : WeightedNakanoNonnegative (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn)) flatMetric φ)
    (hbound : ∀ x ∈ S, inverseCurvatureNormSq (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric φ f x ≤ ENNReal.ofReal C)
    (hφ : ∀ x ∈ S, 0 ≤ φ x)
    (hzero : ∀ x ∉ S, ∀ i : Fin n, ∀ α : Fin 1, coefficients (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn)) f x
      (chartPt (M := ComplexEuclideanManifold n hn) x x) (fun _ => i) α = 0) :
    inverseCurvatureIntegral (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn) φ f ≤
      ENNReal.ofReal (C * (volume : Measure (ComplexVector n)).real (closedBall 0 R)) :=
  inverseCurvatureIntegral_le_support hn R C hR hC φ f S hS hbound hφ
    (fun x hx => half_flat_inverse_zero hn φ f x hN (hzero x hx))

end Yau.Proofs.C03Aux.SourceIntegral
