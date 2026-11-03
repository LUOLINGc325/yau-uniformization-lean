import Yau.Proofs.C05GradientFlowGradient

/-! The computed gradient has the actual inverse-metric covector norm. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem realNormSq_realGrad_eq_inverse_metric (k : HermitianField M)
    (f : M.Carrier → ℝ) (x : M.Carrier) :
    realNormSq k x (realGrad k f x) =
      ∑ a : RIdx n, ∑ b : RIdx n,
        (realMetricFn k x (chartPt x x))⁻¹ a b *
          rDeriv (inChart x f) (chartPt x x) a *
          rDeriv (inChart x f) (chartPt x x) b := by
  let z := chartPt x x
  let G := realMetricFn k x z
  let D : RIdx n → ℝ := fun a => rDeriv (inChart x f) z a
  let W : RIdx n → ℝ := realGradComponent k f x z
  have hGW : G *ᵥ W = D := by
    change G *ᵥ (G⁻¹ *ᵥ D) = D
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G
      (isUnit_iff_ne_zero.mpr (realMetricFn_posDef k x z (mem_extChartAt_target x)).det_pos.ne'),
      Matrix.one_mulVec]
  have hq := realMetricTensor_quadratic k x (realGrad k f x)
  simp only [realGrad, tangentCoords_chartVec x x (mem_extChartAt_source x),
    realCoord_realGradInChart] at hq
  change (∑ a, ∑ b, G a b * W a * W b) = realNormSq k x (realGrad k f x) at hq
  rw [← hq]
  calc
    _ = ∑ a, W a * (G *ᵥ W) a := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, W a * D a := by rw [hGW]
    _ = _ := by
      simp only [W, realGradComponent, D, z, G, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

theorem realNorm_realGrad_eq_inverse_metric (k : HermitianField M)
    (f : M.Carrier → ℝ) (x : M.Carrier) :
    realNorm k x (realGrad k f x) = Real.sqrt
      (∑ a : RIdx n, ∑ b : RIdx n,
        (realMetricFn k x (chartPt x x))⁻¹ a b *
          rDeriv (inChart x f) (chartPt x x) a *
          rDeriv (inChart x f) (chartPt x x) b) := by
  unfold realNorm
  rw [realNormSq_realGrad_eq_inverse_metric]

end Yau.Proofs.C05GradientFlowAux
