import Yau.Proofs.C07RadialCurveMetric

open scoped Manifold Topology Matrix ComplexOrder

noncomputable section

namespace Yau.Proofs.C07CurveLengthAux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- Scaled matrix order controls the norm of every actual tangent vector. -/
theorem hermitianNormSq_le_mul {k₁ k₀ : HermitianField M} {p : M.Carrier} {A : ℝ}
    (horder : HermLE (gMat k₁ p) ((A : ℂ) • gMat k₀ p)) (v : TangentVector M p) :
    hermitianNormSq (k₁ p) v ≤ A * hermitianNormSq (k₀ p) v := by
  let w := tangentCoords p p v
  have hquad (k : HermitianField M) :
      (star (WithLp.ofLp w) ⬝ᵥ (gMat k p *ᵥ WithLp.ofLp w)).re =
        hermitianNormSq (k p) v := by
    rw [gMat, C07RadialCurveAux.chart_quadratic_norm k p p (mem_extChartAt_source p)]
    exact congrArg (hermitianNormSq (k p))
      (C07RadialCurveAux.chartVec_tangentCoords p p (mem_extChartAt_source p) v)
  have h := (Complex.nonneg_iff.mp (horder.dotProduct_mulVec_nonneg (WithLp.ofLp w))).1
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hquad, sub_nonneg] using h

/-- The speed comparison uses the same curve and the actual metric speed,
including at parameters where the total derivative is assigned its default value. -/
theorem curveSpeed_le_sqrt_mul {k₁ k₀ : HermitianField M} {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) {A : ℝ} (hA : 0 ≤ A) (t : ℝ)
    (horder : HermLE (gMat k₁ (γ t)) ((A : ℂ) • gMat k₀ (γ t))) :
    curveSpeed k₁ γ t ≤ Real.sqrt A * curveSpeed k₀ γ t := by
  have hq := hermitianNormSq_le_mul horder (realTangentDerivative γ t)
  unfold curveSpeed
  calc
    _ ≤ Real.sqrt (A * (2 * hermitianNormSq (k₀ (γ t)) (realTangentDerivative γ t))) :=
      Real.sqrt_le_sqrt (by linarith)
    _ = _ := Real.sqrt_mul hA _

end Yau.Proofs.C07CurveLengthAux
