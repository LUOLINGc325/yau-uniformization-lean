import Yau.LeafProofs.L23CovectorNaturality
import Yau.LeafProofs.L23CovectorCurvature

/-! Coordinate naturality of the original curvature coefficients, derived
from the original connection rather than a replacement tensor connection. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem coordinateCovector_curvature_alt_form
    (h : HermitianField M) (hh : MetricSmooth h) (d : M.Carrier)
    (ell : RIdx n) {y : ComplexVector n} (hy : y ∈ chartTarget d) :
    tensorAltFirstTwo (tensorEvalCLM (covariantD h d (covariantD h d
      (fun _ => coordinateCovectorTensor ell)) y))=
      tensorEvalCLM (fun v : Fin 3 → RIdx n =>
        -riemannCoeff h d y (v 0) (v 1) (v 2) ell) := by
  rw [covector_curvature_alt_form h hh d (fun _ => coordinateCovectorTensor ell)
    hy (fun _ => contDiffAt_const)]
  congr 1
  funext v
  simp [coordinateCovectorTensor]

theorem pulledCoordinateCovector_curvature_change
    (h : HermitianField M) (hh : MetricSmooth h) (c d : M.Carrier)
    (ell : RIdx n) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    tensorEvalCLM (fun v : Fin 3 → RIdx n =>
      -∑ b, riemannCoeff h c z (v 0) (v 1) (v 2) b*
        realCoord (fderiv ℝ (L12Aux.realChartChange c d) z (realVec b)) ell)=
      (tensorEvalCLM (fun v : Fin 3 → RIdx n =>
        -riemannCoeff h d (L12Aux.realChartChange c d z) (v 0) (v 1) (v 2) ell)).compContinuousLinearMap
          (fun _ : Fin 3 => fderiv ℝ (L12Aux.realChartChange c d) z) := by
  have heq := congrArg tensorAltFirstTwo
    (coordinateCovector_secondDerivative_change h hh c d ell hz hy)
  have hzD : L12Aux.realChartChange c d z ∈ chartTarget d :=
    (extChartAt (ComplexModel n) d).map_source hy
  have hAp (v : Fin 1 → RIdx n) : ContDiffAt ℝ 2
      (fun w => pulledCoordinateCovector (L12Aux.realChartChange c d) ell w v) z :=
    (pulledCoordinateCovector_contDiffAt _ ell z
      (L12Aux.realChartChange_contDiffAt c d hz hy) v).of_le (by simp)
  rw [tensorAltFirstTwo_comp,
    coordinateCovector_curvature_alt_form h hh d ell hzD,
    covector_curvature_alt_form h hh c
      (pulledCoordinateCovector (L12Aux.realChartChange c d) ell) hz hAp] at heq
  exact heq

theorem riemannCoeff_chart_change
    (h : HermitianField M) (hh : MetricSmooth h) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source)
    (i j k ell : RIdx n) :
    (∑ p, realCoord (fderiv ℝ (L12Aux.realChartChange c d) z (realVec p)) ell*
      riemannCoeff h c z i j k p)=
      ∑ a, ∑ b, ∑ e,
        realCoord (fderiv ℝ (L12Aux.realChartChange c d) z (realVec i)) a*
        realCoord (fderiv ℝ (L12Aux.realChartChange c d) z (realVec j)) b*
        realCoord (fderiv ℝ (L12Aux.realChartChange c d) z (realVec k)) e*
        riemannCoeff h d (L12Aux.realChartChange c d z) a b e ell := by
  have heq := congrArg (fun T : RealTensorForm n 3 => T ![realVec i,realVec j,realVec k])
    (pulledCoordinateCovector_curvature_change h hh c d ell hz hy)
  have hb (A : CovTensor n 3) :
      tensorEvalCLM A ![realVec i,realVec j,realVec k]=A ![i,j,k] := by
    convert tensorEvalCLM_basis A ![i,j,k] using 1
    congr 1
    funext s
    fin_cases s <;> rfl
  rw [hb,ContinuousMultilinearMap.compContinuousLinearMap_apply] at heq
  have hv : (fun s : Fin 3 => fderiv ℝ (L12Aux.realChartChange c d) z
      (![realVec i,realVec j,realVec k] s))=
      ![fderiv ℝ (L12Aux.realChartChange c d) z (realVec i),
        fderiv ℝ (L12Aux.realChartChange c d) z (realVec j),
        fderiv ℝ (L12Aux.realChartChange c d) z (realVec k)] := by
    funext s
    fin_cases s <;> rfl
  rw [hv,tensorEvalCLM_three] at heq
  have heq' := congrArg Neg.neg heq
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.tail_cons,Matrix.head_cons,neg_mul,←Finset.sum_neg_distrib,neg_neg] at heq'
  convert heq' using 1 <;>
    apply Finset.sum_congr rfl <;> intro a ha
  · ring
  · apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro e _
    ring

end Yau.LeafProofs.L23Aux
