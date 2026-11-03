import Yau.Proofs.F01LogDetCurve
import Yau.Proofs.F01NativeMetricEvolution

/-! The actual native metric equation gives the original logarithmic
determinant-ratio time derivative, with scalar curvature and its exact sign. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def flowLogDetRatio (α : HermitianField M) (h : ℝ → HermitianField M)
    (x : M.Carrier) (t : ℝ) : ℝ :=
  Real.log ((gMat (h t) x).det.re / (gMat α x).det.re)

theorem native_logdet_ratio_hasDerivWithinAt
    (α : HermitianField M) (h : ℝ → HermitianField M) (x : M.Carrier) {I : Set ℝ} {t : ℝ}
    (hmetric : ∀ i j, HasDerivWithinAt (fun s => gMat (h s) x i j) (-ricci (h t) x i j) I t) :
    HasDerivWithinAt (flowLogDetRatio α h x) (-scalarCurvature (h t) x) I t := by
  have hpos (s : ℝ) : (gMat (h s) x).PosDef :=
    Yau.LeafProofs.L12Aux.hMat_posDef (h s) x (chartPt x x) (mem_extChartAt_target x)
  have hα : (gMat α x).PosDef :=
    Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hh := (logdet_curve_hasDerivWithinAt (fun s => gMat (h s) x) (-ricci (h t) x)
    hmetric (hpos t)).sub_const (Real.log (gMat α x).det.re)
  have hderiv : traceWith (gMat (h t) x) (-ricci (h t) x) = -scalarCurvature (h t) x := by
    simp only [traceWith, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re, scalarCurvature]
  have hfun : flowLogDetRatio α h x = fun s => Real.log (gMat (h s) x).det.re - Real.log (gMat α x).det.re := by
    funext s
    exact Real.log_div (Complex.pos_iff.mp (hpos s).det_pos).1.ne'
      (Complex.pos_iff.mp hα.det_pos).1.ne'
  rw [hfun]
  simpa only [hderiv] using hh

end Yau.NodeProofs.F01Aux
