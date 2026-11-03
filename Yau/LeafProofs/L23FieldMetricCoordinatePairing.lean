import Yau.LeafProofs.L23FieldMetricNormalDistanceSmooth

/-! Physical metric pairings are invariant under actual coordinate changes and separate vectors. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem realMetricInChart_coordinates_change
    (h : HermitianField M) (a b y : M.Carrier)
    (ha : y ∈ (chartAt (ComplexVector n) a).source)
    (hb : y ∈ (chartAt (ComplexVector n) b).source) (u v : ComplexVector n) :
    realMetricInChart h a (chartPt a y) u v = realMetricInChart h b (chartPt b y)
      (fderiv ℝ (realChartChange a b) (chartPt a y) u)
      (fderiv ℝ (realChartChange a b) (chartPt a y) v) := by
  have hz : chartPt a y ∈ chartTarget a :=
    (extChartAt (ComplexModel n) a).map_source (by simpa only [extChartAt_source] using ha)
  have hinv : chartInv a (chartPt a y) = y :=
    (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using ha)
  have hy : chartInv a (chartPt a y) ∈ (extChartAt (ComplexModel n) b).source := by
    rw [hinv]
    simpa only [extChartAt_source] using hb
  have Hdu (w : ComplexVector n) : fderiv ℝ (realChartChange a b) (chartPt a y) w =
      realTangentCoords b y (realCoordinateField a w y) := by
    have H := realChartChange_fderiv a b hz hy w
    rw [hinv] at H
    exact H
  rw [Hdu,Hdu,realMetricInChart_tangentCoords h b y hb]
  have H := realMetricInChart_tangentCoords h a y ha (realCoordinateField a u y) (realCoordinateField a v y)
  simpa only [realTangentCoords_realCoordinateField a y ha] using H

theorem realMetricInChart_quadratic_eq_zero_iff
    (h : HermitianField M) (c y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) c).source) (v : ComplexVector n) :
    realMetricInChart h c (chartPt c y) v v = 0 ↔ v = 0 := by
  letI := underlyingRealTangentNormedAddCommGroup h y
  letI := underlyingRealTangentInnerProductSpace h y
  constructor
  · intro Hzero
    have H := realMetricInChart_tangentCoords h c y hy (realCoordinateField c v y) (realCoordinateField c v y)
    simp only [realTangentCoords_realCoordinateField c y hy] at H
    have Hphysical : inner ℝ (realCoordinateField c v y) (realCoordinateField c v y) = 0 :=
      H.symm.trans Hzero
    have Hv : realCoordinateField c v y = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp Hphysical
    have Hcoord := congrArg (realTangentCoords c y) Hv
    simpa only [realTangentCoords_realCoordinateField c y hy,map_zero] using Hcoord
  · rintro rfl
    simp

theorem realMetricInChart_pairings_injective
    (h : HermitianField M) (c y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) c).source) {u v : ComplexVector n}
    (H : ∀ w : ComplexVector n, realMetricInChart h c (chartPt c y) u w =
      realMetricInChart h c (chartPt c y) v w) : u = v := by
  apply sub_eq_zero.mp
  apply (realMetricInChart_quadratic_eq_zero_iff h c y hy (u-v)).mp
  calc
    _ = realMetricInChart h c (chartPt c y) u (u-v)-
        realMetricInChart h c (chartPt c y) v (u-v) :=
      congrArg (fun A : ComplexVector n →L[ℝ] ℝ => A (u-v))
        (map_sub (realMetricInChart h c (chartPt c y)) u v)
    _ = 0 := sub_eq_zero.mpr (H (u-v))

end Yau.LeafProofs.L23Aux
