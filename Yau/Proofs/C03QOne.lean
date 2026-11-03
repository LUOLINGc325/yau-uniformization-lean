import Yau.Proofs.C03QOneVariational
import Yau.Proofs.C03FlatComplete

/-! Actual q=1 inverse-curvature control and complete Jacobian cancellation. -/
noncomputable section
open scoped Matrix ComplexOrder Manifold ENNReal
namespace Yau.Proofs.C03Aux.QOne
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.Proofs.P04Aux BundleDbar
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem euclidean_levi (hn : 1 ≤ n) (φ : ComplexVector n → ℝ) (x : ComplexVector n) :
    levi (M := ComplexEuclideanManifold n hn) φ x = leviC φ x := by
  have hc : inChart (M := ComplexEuclideanManifold n hn) x φ = φ := by
    funext z
    change φ ((extChartAt (ComplexModel n) (x : ComplexVector n)).symm z) = φ z
    rw [extChartAt_model_space_eq_id]
    rfl
  change leviC (inChart (M := ComplexEuclideanManifold n hn) x φ)
    (chartPt (M := ComplexEuclideanManifold n hn) x x) = leviC φ x
  rw [hc, FlatComplete.euclidean_chartPt]

theorem inverseCurvatureNormSq_le (hn : 1 ≤ n) (φ : ComplexVector n → ℝ)
    (f : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 1)
    (x : ComplexVector n) (H : Herm n) (hH : H.PosDef) (τ : ℝ) (hτ : 0 < τ)
    (hLevi : HermLE ((τ : ℂ) • H) (leviC φ x)) :
    inverseCurvatureNormSq (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric φ f x ≤
      ENNReal.ofReal ((2 : ℝ) ^ n / τ * ellipsoidQuadratic H⁻¹
        (WithLp.toLp 2 (fun i => coefficients (r := 1)
          (CanonicalCoefficients (ComplexEuclideanManifold n hn))
          f x (chartPt (M := ComplexEuclideanManifold n hn) x x) (fun _ => i) (0 : Fin 1)))) := by
  apply inverseCurvatureNormSq_half_flat_le
    (FlatComplete.euclideanCompleteMetric n hn).form φ f x
    (FlatComplete.euclidean_gMat n hn x) H hH τ hτ
  rwa [euclidean_levi]

theorem inverseCurvatureNormSq_pullback_le (hn : 1 ≤ n) (φ : ComplexVector n → ℝ)
    (f : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 1)
    (x : ComplexVector n) (J Ht : Herm n) (hJ : IsUnit J.det) (hHt : Ht.PosDef)
    (τ : ℝ) (hτ : 0 < τ)
    (hLevi : HermLE ((τ : ℂ) • (Jᴴ * Ht * J)) (leviC φ x))
    (s : ℂ) (Ft : ComplexVector n)
    (hF : WithLp.toLp 2 (fun i => coefficients (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      f x (chartPt (M := ComplexEuclideanManifold n hn) x x) (fun _ => i) (0 : Fin 1)) = s • matrixFiberMap Jᴴ Ft) :
    inverseCurvatureNormSq (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric φ f x ≤
      ENNReal.ofReal ((2 : ℝ) ^ n / τ *
        (‖s‖ ^ 2 * ellipsoidQuadratic Ht⁻¹ Ft)) := by
  have hi : Function.Injective J.mulVec := by
    intro u v huv
    have ht := congrArg (fun w => J⁻¹ *ᵥ w) huv
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ,
      Matrix.one_mulVec] using ht
  have hp := hHt.conjTranspose_mul_mul_same hi
  have hb := inverseCurvatureNormSq_le hn φ f x (Jᴴ * Ht * J) hp τ hτ hLevi
  rwa [hF, quadratic_pullback_cancel J Ht hJ] at hb

end Yau.Proofs.C03Aux.QOne
