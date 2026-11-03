import Yau.Proofs.F01RestartBoundedGeometry

/-! Restrict the actual bounded atlas to a fixed smaller radius.
Charts, native metric and all-order coefficient bounds stay the same;
this realizes the spatial core used by the endpoint estimates. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def shrunkBoundedChartFamily (A : BoundedChartFamily g) (r : ℝ)
    (hr : 0 < r) (hrA : r ≤ A.radius) : BoundedChartFamily g where
  radius := r
  radius_pos := hr
  bound := A.bound
  bound_pos := A.bound_pos
  chart := A.chart
  center := A.center
  closedBall_source := fun a => (closedBall_subset_closedBall hrA).trans (A.closedBall_source a)
  differentiable := A.differentiable
  inverse_differentiable := A.inverse_differentiable
  comparison := fun a z hz => A.comparison a z (ball_subset_ball hrA hz)
  coefficient_smooth := fun a i j => (A.coefficient_smooth a i j).mono (ball_subset_ball hrA)
  coefficient_bound := fun a k z hz i j => A.coefficient_bound a k z (ball_subset_ball hrA hz) i j

theorem restart_geometry_on_actual_smaller_charts
    (g k : HermitianField M) (hk : MetricSmooth k) (A : BoundedChartFamily g)
    {r C : ℝ} (hr : 0 < r) (hrA : r ≤ A.radius) (hC : 0 < C)
    (hRelative : ∀ x, (gMat k x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat k x).PosSemidef)
    (B : ℕ → ℝ)
    (hJets : ∀ a q z, z ∈ ball (0 : ComplexVector n) r → ∀ i j,
      ‖iteratedFDeriv ℝ q (fun w => pullbackMatrix k (A.chart a) w i j) z‖ ≤ B q) :
    Yau.LeafCandidates.HermitianBoundedGeometry k ∧ IsCompleteDistance (inducedDistance k) :=
  restart_geometry_from_actual_chart_jets g k hk (shrunkBoundedChartFamily A r hr hrA) hC hRelative B hJets

end Yau.NodeProofs.F01Aux
