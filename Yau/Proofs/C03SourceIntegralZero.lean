import Yau.Proofs.P04PoleCurvatureEnergy

/-! Vanishing actual centered coefficients make the genuine variational inverse zero. -/
noncomputable section
open scoped Manifold ENNReal
namespace Yau.Proofs.C03Aux.SourceIntegral
open Yau Yau.LeafProofs Yau.Proofs.P04Aux BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

theorem inverse_zero_of_centered_coefficients (g : HermitianField M)
    (φ : M.Carrier → ℝ)
    (f : NQForm (CanonicalCoefficients M) 1) (x : M.Carrier)
    (hN : WeightedNakanoNonnegative (r := 1) (CanonicalCoefficients M) flatMetric φ)
    (hzero : ∀ i : Fin n, ∀ α : Fin 1,
      coefficients (r := 1) (CanonicalCoefficients M) f x
        (chartPt (M := M) x x) (fun _ => i) α = 0) :
    inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g flatMetric φ f x = 0 := by
  have hF : (fun i α => coefficients (r := 1) (CanonicalCoefficients M) f x
      (chartPt (M := M) x x) (fun _ => i) α) = 0 := by
    funext i α
    exact hzero i α
  apply le_antisymm
  · apply iSup_le
    intro V
    change ENNReal.ofReal (2 * (coefficientInner (r := 1) (CanonicalCoefficients M)
      g flatMetric x (fun i α => coefficients (r := 1) (CanonicalCoefficients M)
        f x (chartPt (M := M) x x) (fun _ => i) α) V).re -
        curvatureEnergy (r := 1) (CanonicalCoefficients M) g flatMetric φ x V) ≤ 0
    rw [hF]
    have he := L14Aux.curvatureEnergy_nonneg (CanonicalCoefficients M) g flatMetric φ hN x V
    simp only [coefficientInner, Pi.zero_apply, star_zero, zero_mul,
      Finset.sum_const_zero, mul_zero, Complex.zero_re, zero_sub]
    exact (ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr he)).le
  · exact bot_le

end Yau.Proofs.C03Aux.SourceIntegral
