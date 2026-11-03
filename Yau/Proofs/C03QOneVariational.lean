import Yau.Proofs.C03QOneFlat

/-! Direct control of the original q=1 variational inverse at a single point. -/
noncomputable section
open scoped Matrix ComplexOrder Manifold ENNReal
namespace Yau.Proofs.C03Aux.QOne
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.Proofs.P04Aux BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

theorem inverseCurvatureNormSq_half_flat_le (g : HermitianField M)
    (φ : M.Carrier → ℝ) (f : NQForm (CanonicalCoefficients M) 1) (x : M.Carrier)
    (hg : gMat g x = ((1 / 2 : ℝ) : ℂ) • (1 : Herm n))
    (H : Herm n) (hH : H.PosDef) (τ : ℝ) (hτ : 0 < τ)
    (hLevi : HermLE ((τ : ℂ) • H) (levi φ x)) :
    inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g flatMetric φ f x ≤
      ENNReal.ofReal ((2 : ℝ) ^ n / τ * ellipsoidQuadratic H⁻¹
        (WithLp.toLp 2 (fun i => coefficients (r := 1) (CanonicalCoefficients M)
          f x (chartPt x x) (fun _ => i) (0 : Fin 1)))) := by
  let F : ComplexVector n := WithLp.toLp 2 (fun i =>
    coefficients (r := 1) (CanonicalCoefficients M) f x (chartPt x x)
      (fun _ => i) (0 : Fin 1))
  apply iSup_le
  intro V
  apply ENNReal.ofReal_le_ofReal
  rw [half_flat_coefficientInner g x hg, half_flat_curvatureEnergy g φ x hg]
  rw [Complex.mul_re,
    show ((((2 : ℝ) : ℂ) ^ (n + 1))).re = (2 : ℝ) ^ (n + 1) by norm_cast,
    show ((((2 : ℝ) : ℂ) ^ (n + 1))).im = 0 by norm_cast]
  simp only [zero_mul, sub_zero]
  let W : ComplexVector n := WithLp.toLp 2 (fun i => V i 0)
  have hL : τ * ellipsoidQuadratic H W ≤ ellipsoidQuadratic (levi φ x) W := by
    have ht := ellipsoidQuadratic_nonneg hLevi W
    change 0 ≤ ellipsoidQuadratic (levi φ x - (τ : ℂ) • H) W at ht
    have hsub : ellipsoidQuadratic (levi φ x - (τ : ℂ) • H) W =
        ellipsoidQuadratic (levi φ x) W - τ * ellipsoidQuadratic H W := by
      unfold ellipsoidQuadratic
      simp only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hsub] at ht
    linarith
  have hy := inverse_quadratic_young H hH τ hτ F ((2 : ℂ) • W)
  have hp : (star (WithLp.ofLp F) ⬝ᵥ WithLp.ofLp ((2 : ℂ) • W)).re =
      2 * (star (WithLp.ofLp F) ⬝ᵥ WithLp.ofLp W).re := by
    change (star (WithLp.ofLp F) ⬝ᵥ ((2 : ℂ) • WithLp.ofLp W)).re = _
    simp [dotProduct_smul, Complex.mul_re]
  rw [hp, ellipsoidQuadratic_complex_smul] at hy
  norm_num only [Complex.norm_ofNat, Nat.reducePow] at hy
  have hb := mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ (2 : ℝ) ^ n)
  have hmono := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (2 : ℝ) ^ (n + 2))
  change 2 * ((2 : ℝ) ^ (n + 1) * (star (WithLp.ofLp F) ⬝ᵥ WithLp.ofLp W).re) -
      (2 : ℝ) ^ (n + 2) * ellipsoidQuadratic (levi φ x) W ≤
        (2 : ℝ) ^ n / τ * ellipsoidQuadratic H⁻¹ F
  simp only [pow_add, pow_one, show (2 : ℝ) ^ 2 = 4 by norm_num] at hmono ⊢
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (2 *
        (star (WithLp.ofLp F) ⬝ᵥ WithLp.ofLp W).re) -
          τ * (4 * ellipsoidQuadratic H W)) := by nlinarith [hmono]
    _ ≤ _ := by convert hb using 1 <;> ring

end Yau.Proofs.C03Aux.QOne
