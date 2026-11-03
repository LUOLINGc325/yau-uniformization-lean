import Yau.Proofs.F01GradientChartNaturality
import Yau.Proofs.F01DiagonalGradientTrace
import Yau.Proofs.F01ConformalMetric
import Yau.Proofs.F01MetricEntryLog
import Yau.Proofs.F01ConformalRayleighContact

/-! The actual normal-frame conformal gradient is bounded by the metric
trace times its intrinsic conformal gradient norm. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem conformal_normal_gradient_le_trace (g k : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ))) :
    dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2
      (fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i))) ≤
      traceWith (pullbackMatrix k e 0) (pullbackMatrix (conformalField g f) e 0) *
        gradNormSq (conformalField g f) f (e 0) := by
  have hv (i : Fin n) : 0 < values i := by
    have hh := pullback_diagonal_pos k e he hei hs0 i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  have hα : pullbackMatrix (conformalField g f) e 0 =
      (Real.exp (f (e 0)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [conformalField_pullbackMatrix, hvalue]
  have hh := dualNormMat_diagonal_le_trace values hv (Real.exp (f (e 0))) (Real.exp_pos _)
    (fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i))
  rw [← hdiag, ← hα,
    dualNormMat_holomorphic_chart_gradient (conformalField g f) f hf e he hei hs0] at hh
  exact hh

theorem conformal_normal_trace_nonneg (g k : HermitianField M)
    (f : M.Carrier → ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ))) :
    0 ≤ traceWith (pullbackMatrix k e 0) (pullbackMatrix (conformalField g f) e 0) := by
  have hv (i : Fin n) : 0 < values i := by
    have hh := pullback_diagonal_pos k e he hei hs0 i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  rw [conformalField_pullbackMatrix, hvalue, hdiag,
    traceWith_real_diagonal_smul_one values (fun i => (hv i).ne')]
  exact mul_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hv i).le))

end Yau.NodeProofs.F01Aux
