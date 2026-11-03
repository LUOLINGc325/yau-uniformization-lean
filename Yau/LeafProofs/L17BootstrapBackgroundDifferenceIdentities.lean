import Yau.LeafProofs.L17BootstrapBackgroundDifferenceSmooth

/-! Exact zero, collar, and normalization identities for the selected chart. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

namespace Yau.LeafProofs.L17BootstrapBackgroundDifferenceAux
open L17Aux L17HolderAux L17SchauderAux L17SmallTranslationAux L17BootstrapPatchAux

local instance backgroundDifferenceIdentityMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := backgroundDifferenceMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)

def matrixFamily (θ : ComplexVector n) (q : P.centers) (z : ComplexVector n) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ := by
  classical
  exact if q = D.center then matrixSpecial D θ z t else 0

def logFamily (θ : ComplexVector n) (q : P.centers) (z : ComplexVector n) (t : ℝ) : ℝ := by
  classical
  exact if q = D.center then logSpecial D θ z t else 0

def sigmaFamily (q : P.centers) (z : ComplexVector n) (t : ℝ) : ℝ := by
  classical
  exact if q = D.center then normalizationSpecial D 0 z t else 0

theorem matrixFamily_zero (q : P.centers) (z : ComplexVector n) (t : ℝ) :
    matrixFamily D 0 q z t = 0 := by
  simp [matrixFamily,matrixSpecial,cutoffTranslation_zero_parameter]

theorem logFamily_zero (q : P.centers) (z : ComplexVector n) (t : ℝ) :
    logFamily D 0 q z t = 0 := by
  simp [logFamily,logSpecial,cutoffTranslation_zero_parameter]

theorem matrixFamily_collar (θ : ComplexVector n) (q : P.centers) (z : ComplexVector n) (t : ℝ)
    (h : q ≠ D.center ∨ z ∉ tsupport D.bump) : matrixFamily D θ q z t = 0 := by
  rcases h with hq | hz
  · simp [matrixFamily,hq]
  · have hfix := cutoffTranslation_fixed_of_zero D.bump θ (image_eq_zero_of_notMem_tsupport hz)
    simp [matrixFamily,matrixSpecial,hfix]

theorem logFamily_collar (θ : ComplexVector n) (q : P.centers) (z : ComplexVector n) (t : ℝ)
    (h : q ≠ D.center ∨ z ∉ tsupport D.bump) : logFamily D θ q z t = 0 := by
  rcases h with hq | hz
  · simp [logFamily,hq]
  · have hfix := cutoffTranslation_fixed_of_zero D.bump θ (image_eq_zero_of_notMem_tsupport hz)
    simp [logFamily,logSpecial,hfix]

theorem weight_normalization_cancel {z : ComplexVector n} (hz : z ∈ tsupport D.bump) :
    P.weight D.center (P.charts.chart D.center z) *
      chartWeightSum P.charts P.centers P.radius P.radius_pos (P.charts.chart D.center z) = 1 := by
  have hraw := P.charts.chartWeight_one D.center P.radius_pos P.radius_lt
    (mem_image_of_mem _ (ball_subset_closedBall (D.bump_support_ball_quarter hz)))
  have hS := P.charts.one_le_chartWeightSum P.centers P.radius_pos P.radius_lt
    P.covers P.locallyFinite (P.charts.chart D.center z)
  have hne : chartWeightSum P.charts P.centers P.radius P.radius_pos
      (P.charts.chart D.center z) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hS)
  change (chartWeight (P.charts.chart D.center) P.radius P.radius_pos
    (P.charts.chart D.center z) / _) * _ = 1
  rw [div_mul_cancel₀ _ hne,hraw]

end Yau.LeafProofs.L17BootstrapBackgroundDifferenceAux
