import Yau.Proofs.F04ChartCoefficients

open Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L18Aux

/-- At the chart CENTER the physical Laplacian agrees with the actual
 real principal operator using ONLY the genuine local C2 germ. No global
 smoothness across the boundary of a supported domain is required. -/
theorem flowChartPrincipal_operator_center
    {n : ℕ} {M : ComplexManifold n} (h : ℝ → HermitianField M) (x : M.Carrier)
    {v : M.Carrier → ℝ} (hv : ContDiffAt ℝ 2 (inChart x v) (chartPt x x)) (t : ℝ) :
    laplacian (h t) v x =
      ∑ i, ∑ j, flowChartPrincipal h x (chartPt x x,t) i j *
        spatialDD (fun p : Point n => v (chartInv x p.1)) (chartPt x x,t) (realVec i) (realVec j) := by
  have hh := principal_realLaplacian_eq_twice_traceWith (h t) x (mem_extChartAt_target x) hv
  change (∑ i, ∑ j, (realMetricFn (h t) x (chartPt x x))⁻¹ i j *
      fderiv ℝ (fderiv ℝ (inChart x v)) (chartPt x x) (realVec i) (realVec j)) =
    2 * laplacian (h t) v x at hh
  change laplacian (h t) v x =
    ∑ i, ∑ j, (1/2 : ℝ) * (realMetricFn (h t) x (chartPt x x))⁻¹ i j *
      fderiv ℝ (fderiv ℝ (inChart x v)) (chartPt x x) (realVec i) (realVec j)
  calc
    _ = (1/2 : ℝ) * (2 * laplacian (h t) v x) := by ring
    _ = (1/2 : ℝ) * (∑ i, ∑ j, (realMetricFn (h t) x (chartPt x x))⁻¹ i j *
      fderiv ℝ (fderiv ℝ (inChart x v)) (chartPt x x) (realVec i) (realVec j)) := by rw [hh]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end Yau.F04Proof
