import Yau.LeafProofs.L19LocalizationCalculus

/-! The actual scalar Laplacian sign under the local C² hypotheses of the moving bump. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {M : ComplexManifold n}

theorem chartRealLaplacian_eq_twice_laplacian (g : SmoothMetric M) (hK : IsKahler g)
    (u : M.Carrier → ℝ) (x : M.Carrier)
    (hu : ContDiffAt ℝ 2 (inChart x u) (chartPt x x)) :
    chartRealLaplacian g.form x (inChart x u) (chartPt x x) = 2 * laplacian g.form u x := by
  have hh := principal_realLaplacian_eq_twice_traceWith g.form x (mem_extChartAt_target x) hu
  change (∑ i, ∑ j, (realMetricFn g.form x (chartPt x x))⁻¹ i j *
    fderiv ℝ (fderiv ℝ (inChart x u)) (chartPt x x) (realVec i) (realVec j)) =
      2 * laplacian g.form u x at hh
  rw [chartRealLaplacian_eq_principal g hK x (z := chartPt x x)
    (mem_extChartAt_target x) (inChart x u)]
  simpa only [LeafProofs.L18Aux.rDeriv_rDeriv_eq_hessian hu] using hh

theorem laplacian_nonpos_at_chart_local_max (g : SmoothMetric M) (hK : IsKahler g)
    (u : M.Carrier → ℝ) (x : M.Carrier)
    (hu : ContDiffAt ℝ 2 (inChart x u) (chartPt x x))
    (hm : IsLocalMax (inChart x u) (chartPt x x)) : laplacian g.form u x ≤ 0 := by
  have hh := chartRealLaplacian_nonpos_at_local_max g x hu hm
  rw [chartRealLaplacian_eq_twice_laplacian g hK u x hu] at hh
  linarith only [hh]

theorem laplacian_nonpos_at_local_max (g : SmoothMetric M) (hK : IsKahler g)
    (u : M.Carrier → ℝ) (x : M.Carrier)
    (hu : ContDiffAt ℝ 2 (inChart x u) (chartPt x x)) (hm : IsLocalMax u x) :
    laplacian g.form u x ≤ 0 := by
  have hi : ContinuousAt (chartInv x) (chartPt x x) :=
    continuousAt_extChartAt_symm'' (mem_extChartAt_target x)
  have hinv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hm' : IsLocalMax (inChart x u) (chartPt x x) := by
    have hlim : Tendsto (chartInv x) (𝓝 (chartPt x x)) (𝓝 x) := by
      simpa only [hinv] using hi.tendsto
    change ∀ᶠ z in 𝓝 (chartPt x x), inChart x u z ≤ inChart x u (chartPt x x)
    simpa only [inChart, hinv] using hlim.eventually hm
  exact laplacian_nonpos_at_chart_local_max g hK u x hu hm'

end Yau.Proofs.F03Aux
