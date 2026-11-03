import Yau.Proofs.F01OpenDifferential

/-! Smoothness of the genuine restricted metric through equality of its actual
fixed-chart coefficients with the original coefficients on the smaller target. -/
open Set TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem openInclusion_chartVec
    (a : (openConnectedManifold M S hS).Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (v : ComplexVector n) :
    mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) (chartInv a z)
      (chartVec a (chartInv a z) v) = chartVec a.val (chartInv a z).val v := by
  have hp : chartPt a (chartInv a z) = z :=
    (extChartAt (ComplexModel n) a).right_inv hz
  unfold chartVec
  rw [← openInclusion_chartPt M S hS a (chartInv a z), hp]
  exact DFunLike.congr_fun (openInclusion_comp_chartInv_mfderiv M S hS a hz) v

theorem openRestrictedField_realMetricFn (h : HermitianField M)
    (a : (openConnectedManifold M S hS).Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (i j : RIdx n) :
    realMetricFn (openRestrictedField M S hS h) a z i j =
      realMetricFn h a.val z i j := by
  unfold realMetricFn
  rw [openRestrictedField_value, openInclusion_chartVec M S hS a hz,
    openInclusion_chartVec M S hS a hz, openInclusion_chartInv M S hS a hz]

theorem openRestrictedField_metricSmooth {h : HermitianField M}
    (hh : MetricSmooth h) : MetricSmooth (openRestrictedField M S hS h) := by
  intro a i j
  apply ((hh a.val i j).mono (openInclusion_chartTarget_subset M S hS a)).congr
  intro z hz
  exact openRestrictedField_realMetricFn M S hS h a hz i j

end Yau.NodeProofs.F01Aux
