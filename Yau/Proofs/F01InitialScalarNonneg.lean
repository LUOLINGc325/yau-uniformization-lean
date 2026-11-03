import Yau.Proofs.F01ScalarCurvatureChart
import Yau.Proofs.F01RealNormalChart
import Yau.Proofs.F01NormalCurvatureSign
import Yau.Proofs.F01LogDetDiagonalHessian

/-! The actual nonnegative bisectional curvature of the initial Kähler
metric implies nonnegative computed scalar curvature. Normal coordinates
are constructed, and the logarithmic determinant contraction is computed. -/
noncomputable section
open Set
open scoped ContDiff Matrix Manifold ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarCurvature_nonneg_of_nonnegBisectional
    (g : SmoothMetric M) (hcurv : NonnegBisectional g.form) (x : M.Carrier) :
    0 ≤ scalarCurvature g.form x := by
  have hg := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g
  obtain ⟨e, hcenter, hs0, heSmooth, heiSmooth, hvalue, hzero, values, hdiag⟩ :=
    exists_real_normal_holomorphic_chart g g.form x
  have he := heSmooth.mdifferentiableOn (by simp)
  have hei := heiSmooth.mdifferentiableOn (by simp)
  have hH (i j : Fin n) := pullbackMatrix_entry_contDiffOn g.form hg e he i j
  have hpos (z : ComplexVector n) (hz : z ∈ e.source) :=
    pullbackMatrix_posDef g.form e he hei hz
  have hdiagOne : pullbackMatrix g.form e 0 = Matrix.diagonal (fun _ : Fin n => (1 : ℂ)) := by
    simpa using hvalue
  have hwzero (i j a : Fin n) :
      wirt (fun z => pullbackMatrix g.form e z i j) 0 (stdVec a) = 0 := by
    simp only [wirt, hzero, ContinuousLinearMap.zero_apply, mul_zero, sub_self]
  have hlevi (a : Fin n) :
      (leviC (fun z => Real.log (pullbackMatrix g.form e z).det.re) 0 a a).re ≤ 0 := by
    have hh := logdet_diagonal_levi_formula (pullbackMatrix g.form e) e.open_source
      hH hpos hs0 (fun _ => (1 : ℝ)) hdiagOne a
    simp only [inv_one, one_mul, hwzero, Complex.normSq_zero, mul_zero,
      Finset.sum_const_zero, sub_zero] at hh
    rw [hh]
    exact Finset.sum_nonpos (fun i _ => normal_metric_mixed_nonpos g.form hg hcurv
      e he hei hs0 hzero a i)
  have hs : 0 ≤ traceWith (pullbackMatrix g.form e 0) (pullbackRicci g.form e 0) := by
    rw [hvalue]
    change 0 ≤ (Matrix.trace (1⁻¹ *
      -leviC (fun z => Real.log (pullbackMatrix g.form e z).det.re) 0)).re
    simp only [inv_one, Matrix.one_mul, Matrix.trace, Matrix.diag_apply, Matrix.neg_apply,
      Complex.re_sum, Complex.neg_re]
    exact Finset.sum_nonneg (fun i _ => neg_nonneg.mpr (hlevi i))
  rw [scalarCurvature_holomorphic_chart g.form hg e he hei hs0, hcenter] at hs
  exact hs

end Yau.NodeProofs.F01Aux
