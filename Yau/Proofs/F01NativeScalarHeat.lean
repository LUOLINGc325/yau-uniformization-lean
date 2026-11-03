import Yau.Proofs.F01NativeLogDetEvolution
import Yau.Proofs.F01NativeLogDetLevi
import Yau.Proofs.F01HeatChartNaturality

/-! The actual native logarithmic determinant ratio satisfies its source
heat equation, derived from the actual metric equation and Ricci difference. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem native_logdet_ratio_heat_identity
    (α : HermitianField M) (hα : MetricSmooth α) (h : ℝ → HermitianField M)
    {I : Set ℝ} {t : ℝ} (hk : MetricSmooth (h t)) (x : M.Carrier)
    (hUnique : UniqueDiffWithinAt ℝ I t)
    (hmetric : ∀ i j, HasDerivWithinAt (fun s => gMat (h s) x i j) (-ricci (h t) x i j) I t) :
    fieldHeatWithin h I (fun s y => flowLogDetRatio α h y s) x t =
      -traceWith (gMat (h t) x) (ricci α x) := by
  have htime := native_logdet_ratio_hasDerivWithinAt α h x hmetric
  unfold fieldHeatWithin
  rw [htime.derivWithin hUnique]
  change -scalarCurvature (h t) x -
    traceWith (gMat (h t) x) (levi (fun y => Real.log ((gMat (h t) y).det.re / (gMat α y).det.re)) x) = _
  rw [levi_logdet_ratio_native (h t) α hk hα x, traceWith_add]
  simp only [scalarCurvature, traceWith, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re]
  ring

end Yau.NodeProofs.F01Aux
