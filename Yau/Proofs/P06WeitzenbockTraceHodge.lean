import Yau.Proofs.P06WeitzenbockTraceReaction
import Yau.Proofs.P06WeitzenbockTypeHodge

noncomputable section
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem hodge_oneOne (g : SmoothMetric M) (μ : MeasureTheory.Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A) :
    RealOneOne (L03.hodgeRealForm g.form 2 A) := by
  have he := hodge_oneOneProjection g μ hμ hk A hA
  rw [oneOneProjection_fixed A h11] at he
  rw [he]
  exact oneOneProjection_type _

/-- Core trace intertwining for the original computed Hodge expressions.
The input is arbitrary smooth real (1,1), with no d-closedness assumption. -/
theorem trace_hodge (g : SmoothMetric M) (μ : MeasureTheory.Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A) :
    scalarForm (formTrace g.form (L03.hodgeRealForm g.form 2 A)) =
      L03.hodgeRealForm g.form 0 (scalarForm (formTrace g.form A)) := by
  have hs := L12Aux.metricSmooth_of_smoothMetric g
  have ht := trace_smooth g.form hs A hA h11
  have hht := hodge_oneOne g μ hμ hk A hA h11
  apply L03.realForm_eq_of_center_components
  intro x I
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hsum (H K L : Matrix (RIdx n) (RIdx n) ℝ) :
      matrixMetricJTrace H (K + L) = matrixMetricJTrace H K + matrixMetricJTrace H L := by
    simp only [matrixMetricJTrace, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, mul_add]
  rw [scalarForm_components, matrixMetricJTrace_form g.form _ hht x hx,
    chartFormMatrix_hodge g.form hs A hA x hx,
    hodgeTwoMatrix_formula g.form hs A hA x hx, hsum,
    trace_curvature_zero g hk A h11 x, add_zero,
    trace_rough_eq_scalarHodge g.form hs hk A hA h11 x hx]
  have he := hodge_represents g.form hs (scalarForm (formTrace g.form A))
    (scalarForm_smooth _ ht) x (chartPt x x) hx I
  have hi : I = Fin.elim0 := by funext i; exact Fin.elim0 i
  rw [hi] at he
  rw [hi]
  exact he.symm

end Yau.NodeProofs.P06Weitzenbock
