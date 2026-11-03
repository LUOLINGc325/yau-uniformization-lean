import Yau.LeafProofs.L05PerturbationSpatialTaylor
import Yau.LeafProofs.L05PerturbationTimeTaylor

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_taylor_remainder {n : ℕ} {sigma C : ℝ} (hs : 0 < sigma) (hs1 : sigma < 1)
    {h : Point n → ℝ} (hh : SchauderBound sigma (backward (1/4)) h C)
    {r : ℝ} (hr : 0 < r) (hrb : r ≤ 1/8) :
    ∀ p∈perturbClosed (0 : Space n) r 0,
      |h p-perturbTaylor (backward (1/4)) h (0,0) p| ≤ 3*C*r^(2+sigma) := by
  intro p hp
  have hSpace := perturb_spatial_taylor_remainder hs hh hr hrb hp.1
  have hTime := perturb_time_taylor_remainder hs hh hr hrb hp
  have hExpr : h p-perturbTaylor (backward (1/4)) h (0,0) p=
      (h (p.1,0)-perturbPolynomial (h 0) (spatialD h 0) (hessian h 0) 0 (p.1,0))+
      (h p-h (p.1,0)-timeD (backward (1/4)) h 0*p.2) := by
    change h p-perturbTaylor (backward (1/4)) h (0 : Point n) p = _
    rw [perturb_taylor_origin_polynomial hh.1 perturb_quarter_origin p]
    simp only [perturbPolynomial,zero_mul,mul_zero,add_zero]
    ring
  calc
    _ ≤ |h (p.1,0)-perturbPolynomial (h 0) (spatialD h 0) (hessian h 0) 0 (p.1,0)|+
        |h p-h (p.1,0)-timeD (backward (1/4)) h 0*p.2| := by
      rw [hExpr]
      exact abs_add_le _ _
    _ ≤ C*r^sigma*r^2+2*C*r^sigma*r^2 := add_le_add hSpace hTime
    _ = 3*C*r^(2+sigma) := by
      rw [Real.rpow_add hr,Real.rpow_two]
      ring

end Yau.LeafProofs.L05Aux
