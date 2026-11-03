import Yau.LeafProofs.L17PotentialHermitianField
import Yau.LeafProofs.L17BootstrapPositiveBaseHolder

noncomputable section
open Set Metric
open scoped Matrix Topology ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapSmoothAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPositiveBaseHolderAux
local instance flowPullbackMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0<T}

theorem potentialFlowField_background_pullback (hg : MetricSmooth g)
    (hTime : T≤P.radius^2) (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)
    (u : SchauderSpace P T gamma hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (p : P.centers) (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    pullbackMatrix (potentialFlowField hg u hSmall (t : ℝ)) (P.charts.chart p) z=
      Hstar P hT hTime hgamma0 hgamma1 hr u ⟨p,(z,t)⟩ := by
  let y := P.charts.chart p z
  let J := linearMatrix (coordinateDifferential (P.charts.chart p) y z)
  have hPull :
      pullbackMatrix (potentialFlowField hg u hSmall (t : ℝ)) (P.charts.chart p) z=
        Jᴴ*gMat (potentialFlowField hg u hSmall (t : ℝ)) y*J :=
    pullbackMatrix_eq_congruence (potentialFlowField hg u hSmall (t : ℝ))
      (P.charts.chart p) y z (mem_extChartAt_source y)
  rw [gMat_potentialFlowField hg u hSmall t y] at hPull
  rw [Hstar_value]
  exact hPull.trans (coordinateMetricMatrix_eq_congruence hg u ⟨p,(z,t)⟩).symm

end Yau.LeafProofs.L17BootstrapSmoothAux
