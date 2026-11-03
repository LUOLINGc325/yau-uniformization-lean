import Yau.LeafProofs.L17BootstrapPositiveBaseHolderBackground
import Yau.LeafProofs.L17CoordinateMetric

/-! The actual fixed-base metric is a globally smooth affine Banach-valued map. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Yau.LeafProofs.L17BootstrapPositiveBaseHolderAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux

local instance positiveBaseAffineMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) {T gamma : ℝ}

def Hstar (hT : 0 < T) (hTime : T ≤ P.radius^2) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hr : P.radius ≤ 1) (u : SchauderSpace P T gamma hT) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma :=
  backgroundMatrixBanach P hTime hgamma1 hr + potentialLeviBanachCLM P T gamma hT u -
    timeScalarActionCLM P hT hgamma0 (hgamma1.trans (by norm_num)) hr
      (ricciMatrixBanach P hTime hgamma1 hr)

theorem Hstar_value (hT : 0 < T) (hTime : T ≤ P.radius^2) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hr : P.radius ≤ 1) (u : SchauderSpace P T gamma hT)
    (q : LocalCylinder P T) :
    Hstar P hT hTime hgamma0 hgamma1 hr u q =
      pullbackMatrix g (P.charts.chart q.1) q.2.1 + coordinateMetricError u q := by
  change backgroundMatrixBanach P hTime hgamma1 hr q +
    potentialLeviBanachCLM P T gamma hT u q -
    timeScalarActionCLM P hT hgamma0 (hgamma1.trans (by norm_num)) hr
      (ricciMatrixBanach P hTime hgamma1 hr) q = _
  rw [backgroundMatrixBanach_value,potentialLeviBanachCLM_value,timeScalarActionCLM_value,
    ricciMatrixBanach_value,coordinateMetricError_eq,matrixRealScalar_eq_complexScalar]
  abel

theorem Hstar_contDiff (hT : 0 < T) (hTime : T ≤ P.radius^2) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hr : P.radius ≤ 1) :
    ContDiff ℝ ∞ (Hstar P hT hTime hgamma0 hgamma1 hr) := by
  unfold Hstar
  exact (contDiff_const.add (potentialLeviBanachCLM P T gamma hT).contDiff).sub contDiff_const

end Yau.LeafProofs.L17BootstrapPositiveBaseHolderAux
