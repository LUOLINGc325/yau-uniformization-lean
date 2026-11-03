import Yau.Proofs.P03AntiCanonicalCurvature
import Yau.Proofs.P03TangentGriffiths
import Yau.Proofs.P03GriffithsTrace

open scoped Manifold Topology ContDiff ComplexOrder Matrix
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ}

theorem antiCanonical_nakano (X : KahlerManifold n) :
    NakanoNonnegative (r := 1) (AntiCanonicalFiber X.manifold)
      (antiCanonicalMetric X.metric.form) := by
  intro a z hz U
  rw [antiCanonical_localDomain] at hz
  let H := hMat X.metric.form a z
  let R := curvatureMatrix (hMat X.metric.form a) z
  let x := chartInv a z
  have hx : x ∈ (extChartAt (ComplexModel n) a).source :=
    (extChartAt (ComplexModel n) a).map_target hz
  let b := determinantFrameBasis a x hx
  have hGram : H = hermitianGram (X.metric.form x) b := by
    have hi : chartPt a x = z := (extChartAt (ComplexModel n) a).right_inv hz
    change hMat X.metric.form a z = hermitianGram (X.metric.form x) b
    rw [← hi]
    exact hMat_chartFrameGram X.metric.form a x hx
  have hcurv : curvature (r := 1) (AntiCanonicalFiber X.manifold)
      (antiCanonicalMetric X.metric.form) a z = fun i j => H.det •
        (show Matrix (Fin 1) (Fin 1) ℂ from fun _ _ => Matrix.trace (H⁻¹ * R i j)) := by
    funext i j
    ext α β
    exact antiCanonical_curvature X.metric a hz i j α β
  rw [hcurv, L07Aux.nakanoQuadratic_smul_real _ H.det
    (by rw [hGram]; exact L07Aux.hermitianGram_det_im _ _) U]
  apply mul_nonneg
  · exact (Complex.nonneg_iff.mp (hMat_posDef X.metric.form a z hz).posSemidef.det_nonneg).1
  · let ξ : ComplexVector n := WithLp.toLp 2 (fun i => U i 0)
    have he : nakanoQuadratic
        (fun i j => (show Matrix (Fin 1) (Fin 1) ℂ from fun _ _ => Matrix.trace (H⁻¹ * R i j))) U =
        (∑ i, ∑ j, Matrix.trace (H⁻¹ * R i j) * ξ i * star (ξ j)).re := by
      simp only [nakanoQuadratic, Fin.sum_univ_one]
      apply congrArg Complex.re
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change Matrix.trace (H⁻¹ * R i j) * star (U j 0) * U i 0 =
        Matrix.trace (H⁻¹ * R i j) * U i 0 * star (U j 0)
      ring
    rw [he, hGram]
    exact griffiths_metric_trace_nonnegative (X.metric.form x) b R
      (tangent_griffiths_nonnegative X a hz) ξ

end Yau.NodeProofs.P03Aux
