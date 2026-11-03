import Yau.LeafProofs.L23FieldMetricCoordinatePairing
import Yau.LeafProofs.L23FieldMetricNormalDistanceVariation

/-! Actual free vertex curves and the conversion of their coordinate first variations. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

def fieldVertexCurve (c y : M.Carrier) (w : ComplexVector n) (r : ℝ) : M.Carrier :=
  chartInv c (chartPt c y+r • w)

theorem fieldVertexCurve_zero (c y : M.Carrier) (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (w : ComplexVector n) : fieldVertexCurve c y w 0 = y := by
  simp only [fieldVertexCurve,zero_smul,add_zero]
  exact (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hy)

theorem fieldVertexCurve_contMDiffAt (c y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) c).source) (w : ComplexVector n) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞ (fieldVertexCurve c y w) 0 := by
  letI := manifold_realSmooth M
  have hz : chartPt c y ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hy)
  have HI := contMDiffAt_chartInv_real c (chartPt c y) hz
  have HI' : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞
      (chartInv c) (chartPt c y+(0 : ℝ) • w) := by simpa only [zero_smul,add_zero] using HI
  have HL : ContDiffAt ℝ ∞ (fun r : ℝ => chartPt c y+r • w) 0 := by fun_prop
  exact HI'.comp 0 HL.contMDiffAt

theorem fieldVertexCurve_coordinates_hasDerivAt (b c y : M.Carrier)
    (hb : y ∈ (chartAt (ComplexVector n) b).source)
    (hc : y ∈ (chartAt (ComplexVector n) c).source) (w : ComplexVector n) :
    HasDerivAt (fun r => chartPt c (fieldVertexCurve b y w r))
      (fderiv ℝ (realChartChange b c) (chartPt b y) w) 0 := by
  have hz : chartPt b y ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source (by simpa only [extChartAt_source] using hb)
  have hinv : chartInv b (chartPt b y) = y :=
    (extChartAt (ComplexModel n) b).left_inv (by simpa only [extChartAt_source] using hb)
  have hyc : chartInv b (chartPt b y) ∈ (extChartAt (ComplexModel n) c).source := by
    rw [hinv]
    simpa only [extChartAt_source] using hc
  have HT := ((realChartChange_contDiffAt b c hz hyc).differentiableAt (by simp)).hasFDerivAt
  have HT' : HasFDerivAt (realChartChange b c) (fderiv ℝ (realChartChange b c) (chartPt b y))
      (chartPt b y+(0 : ℝ) • w) := by simpa only [zero_smul,add_zero] using HT
  have HL : HasDerivAt (fun r : ℝ => chartPt b y+r • w) w 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (chartPt b y) using 1 <;> simp
  exact HT'.comp_hasDerivAt 0 HL

theorem fieldVertexCurve_coordinates_contDiffAt (b c y : M.Carrier)
    (hb : y ∈ (chartAt (ComplexVector n) b).source)
    (hc : y ∈ (chartAt (ComplexVector n) c).source) (w : ComplexVector n) :
    ContDiffAt ℝ ∞ (fun r => chartPt c (fieldVertexCurve b y w r)) 0 := by
  letI := manifold_realSmooth M
  have hβ₀ : fieldVertexCurve b y w 0 = y := fieldVertexCurve_zero b y hb w
  have hsource : fieldVertexCurve b y w 0 ∈ (chartAt (ComplexVector n) c).source := by
    rw [hβ₀]
    exact hc
  have Hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞
      (chartPt c) (fieldVertexCurve b y w 0) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (x := c) (x' := fieldVertexCurve b y w 0) hsource) using 1
  exact (Hchart.comp 0 (fieldVertexCurve_contMDiffAt b y hb w)).contDiffAt

theorem realMetricInChart_coordinates_change_one_argument
    (h : HermitianField M) (a b y : M.Carrier)
    (ha : y ∈ (chartAt (ComplexVector n) a).source)
    (hb : y ∈ (chartAt (ComplexVector n) b).source) (u w : ComplexVector n) :
    realMetricInChart h a (chartPt a y) u (fderiv ℝ (realChartChange b a) (chartPt b y) w) =
      realMetricInChart h b (chartPt b y) (fderiv ℝ (realChartChange a b) (chartPt a y) u) w := by
  have hz : chartPt b y ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source (by simpa only [extChartAt_source] using hb)
  have hinv : chartInv b (chartPt b y) = y :=
    (extChartAt (ComplexModel n) b).left_inv (by simpa only [extChartAt_source] using hb)
  have hya : chartInv b (chartPt b y) ∈ (extChartAt (ComplexModel n) a).source := by
    rw [hinv]
    simpa only [extChartAt_source] using ha
  have Hinv := realChartChange_fderiv_inverse b a hz hya w
  have Hpoint : realChartChange b a (chartPt b y) = chartPt a y := by
    change chartPt a (chartInv b (chartPt b y)) = chartPt a y
    rw [hinv]
  rw [Hpoint] at Hinv
  have H := realMetricInChart_coordinates_change h a b y ha hb u
    (fderiv ℝ (realChartChange b a) (chartPt b y) w)
  rwa [Hinv] at H

end Yau.LeafProofs.L23Aux
