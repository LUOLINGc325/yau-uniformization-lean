import Yau.Proofs.F01NativeLogDetEvolution
import Yau.Proofs.F01MetricFamilyEntries
import Yau.Proofs.F01MetricFamilySlices
import Yau.Proofs.F01OrdinaryPullback

/-! The original determinant quotient has genuine native joint
smoothness; coordinate Jacobian factors cancel from this actual scalar. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem flowLogDetRatio_chart_eq (α : HermitianField M) (h : ℝ → HermitianField M)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (t : ℝ) :
    flowLogDetRatio α h (chartInv x z) t =
      Real.log ((hMat (h t) x z).det.re / (hMat α x z).det.re) := by
  let e := ordinaryChart x
  have he := (ordinaryChart_contMDiffOn x).mdifferentiableOn (by simp)
  have hei := (ordinaryChart_inverse_contMDiffOn x).mdifferentiableOn (by simp)
  have hze : z ∈ e.source := by rw [ordinaryChart_source]; exact hz
  have hr := pullbackMatrix_determinant_ratio (h t) α e he hei (e z) hze (mem_extChartAt_source (e z))
  change (pullbackMatrix (h t) e z).det.re / (pullbackMatrix α e z).det.re =
    (gMat (h t) (e z)).det.re / (gMat α (e z)).det.re at hr
  rw [ordinaryChart_pullbackMatrix (h t) x hz, ordinaryChart_pullbackMatrix α x hz,
    ordinaryChart_apply] at hr
  exact congrArg Real.log hr.symm

theorem flowLogDetRatio_smoothSpaceTime (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) {I : Set ℝ} (hh : MetricFamilySmooth h I) :
    SmoothSpaceTime (flowLogDetRatio α h) I := by
  intro x
  have hnum : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (hMat (h p.2) x p.1).det.re)
      (chartTarget x ×ˢ I) := Complex.reCLM.contDiff.comp_contDiffOn
    (Yau.LeafProofs.L12Aux.contDiffOn_matrix_det (fun i j => metricFamily_hMat_contDiffOn h hh x i j))
  have hden : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (hMat α x p.1).det.re)
      (chartTarget x ×ˢ I) := Complex.reCLM.contDiff.comp_contDiffOn
    (Yau.LeafProofs.L12Aux.contDiffOn_matrix_det (fun i j =>
      metricFamily_hMat_contDiffOn (fun _ => α) (metricFamilySmooth_const hα I) x i j))
  have hratio := hnum.div hden (fun p hp => (Yau.LeafProofs.L12Aux.hMat_det_re_pos α x hp.1).ne')
  have hlog := hratio.log (fun p hp => (div_pos
    (Yau.LeafProofs.L12Aux.hMat_det_re_pos (h p.2) x hp.1)
    (Yau.LeafProofs.L12Aux.hMat_det_re_pos α x hp.1)).ne')
  apply hlog.congr
  intro p hp
  exact flowLogDetRatio_chart_eq α h x hp.1 p.2

theorem flowLogDetRatio_initial (α : HermitianField M) (h : ℝ → HermitianField M)
    (hh0 : h 0 = α) (x : M.Carrier) : flowLogDetRatio α h x 0 = 0 := by
  have hp : 0 < (gMat α x).det.re :=
    Yau.LeafProofs.L12Aux.hMat_det_re_pos α x (mem_extChartAt_target x)
  simp only [flowLogDetRatio, hh0, div_self hp.ne', Real.log_one]

end Yau.NodeProofs.F01Aux
