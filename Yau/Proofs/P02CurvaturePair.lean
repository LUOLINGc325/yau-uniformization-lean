import Yau.Proofs.P02ParallelJ
import Yau.LeafProofs.L23DistanceEnergyCurvatureForm
import Yau.LeafProofs.L23DistanceEnergyTraceBound
import Yau.LeafProofs.L23RmNaturality

noncomputable section
open scoped Topology ContDiff Manifold Matrix

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux
variable {n : ℕ} {M : ComplexManifold n}

def coordinateRm (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (U V W T : ComplexVector n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, curvature4 h c z i j k l *
    realCoord U i * realCoord V j * realCoord W k * realCoord T l

def coordinateBisectional (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (T V : ComplexVector n) : ℝ :=
  coordinateRm h c z T V V T +
    coordinateRm h c z T (Complex.I • V) (Complex.I • V) T

/-- Direct expansion of the canonical tensor, with the same coefficient
rearrangement as the certified G01 real-curvature calculator. -/
theorem paperRm_eq_coordinateRm (h : HermitianField M) (x : M.Carrier)
    (U V W T : TangentVector M x) :
    paperRm h x U V W T = coordinateRm h x (chartPt x x)
      (tangentCoords x x U) (tangentCoords x x V)
      (tangentCoords x x W) (tangentCoords x x T) := by
  unfold paperRm coordinateRm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [curvature4, Finset.sum_mul]

theorem coordinateRm_swap_first (h : HermitianField M) (c : M.Carrier)
    (z U V W T : ComplexVector n) :
    coordinateRm h c z U V W T = -coordinateRm h c z V U W T := by
  unfold coordinateRm
  simp only [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [curvature4_swap_first h c z j i k l]
  ring

theorem connectionCurvature_pair_eq_coordinateRm (h : HermitianField M)
    (hs : MetricSmooth h) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (U V W T : ComplexVector n) :
    realMetricInChart h c z (connectionCurvature (chartChristoffelBilin h c) z U V W) T =
      coordinateRm h c z U V W T := by
  rw [connectionCurvature_pair_eq_sum h hs c hz]
  unfold coordinateRm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change (realCoord U i * realCoord V j * realCoord W k * realCoord T l) *
      curvature4 h c z i j k l = _
  ring

theorem connectionCurvature_sectional_sign (h : HermitianField M)
    (hs : MetricSmooth h) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (T V : ComplexVector n) :
    realMetricInChart h c z T (connectionCurvature (chartChristoffelBilin h c) z V T V) =
      -coordinateRm h c z T V V T := by
  rw [realMetricInChart_symm h c z,
    connectionCurvature_pair_eq_coordinateRm h hs c hz]
  exact coordinateRm_swap_first h c z V T V T

theorem connectionCurvature_bisectional_sign (h : HermitianField M)
    (hs : MetricSmooth h) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (T V : ComplexVector n) :
    realMetricInChart h c z T (connectionCurvature (chartChristoffelBilin h c) z V T V) +
      realMetricInChart h c z T
        (connectionCurvature (chartChristoffelBilin h c) z (Complex.I • V) T (Complex.I • V)) =
      -coordinateBisectional h c z T V := by
  rw [connectionCurvature_sectional_sign h hs c hz,
    connectionCurvature_sectional_sign h hs c hz]
  unfold coordinateBisectional
  ring

theorem realMetricInChart_I_I (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (v : ComplexVector n) :
    realMetricInChart h c z (Complex.I • v) (Complex.I • v) =
      realMetricInChart h c z v v := by
  have H (V : TangentVector M (chartInv c z)) :
      (h (chartInv c z)).toFun (Complex.I • V) (Complex.I • V) =
        (h (chartInv c z)).toFun V V := by
    rw [(h (chartInv c z)).map_smul_left, (h (chartInv c z)).map_smul_right]
    rw [show star (Complex.I : ℂ) = -Complex.I by simp]
    calc
      _ = ((-Complex.I) * Complex.I) * (h (chartInv c z)).toFun V V := by ring
      _ = _ := by simp
  simp only [realMetricInChart_apply, underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec c z (Complex.I • v) hz,
    realTangentEquiv_realChartVec c z v hz, chartVec_complex_smul]
  rw [H]

theorem paperBisectional_eq_coordinate (h : HermitianField M) (x : M.Carrier)
    (U V : TangentVector M x) :
    paperBisectionalNumerator h x U V =
      coordinateBisectional h x (chartPt x x) (tangentCoords x x U) (tangentCoords x x V) := by
  unfold paperBisectionalNumerator paperComplexStructure coordinateBisectional
  rw [paperRm_eq_coordinateRm, paperRm_eq_coordinateRm]
  congr 1
  unfold tangentCoords
  simp only [map_smul]
  rfl

end Yau.NodeProofs.P02Aux
