import Yau.Proofs.F01LocalFlowTime
import Yau.Proofs.F01OrdinaryPullback

/-! The actual scalar potential equation implies the original native
matrix metric equation, with its original Ricci sign. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem flow_potential_native_metric_hasDerivAt
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {I : Set ℝ} (hI : IsOpen I) (hU : SmoothSpaceTime U I)
    (hpot : ∀ s ∈ I, ∀ x, gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ I → HasDerivAt (U x)
      (Real.log ((gMat (h s) x).det.re / (gMat α x).det.re)) s)
    (x : M.Carrier) {t : ℝ} (ht : t ∈ I) (i j : Fin n) :
    HasDerivAt (fun s => gMat (h s) x i j) (-ricci (h t) x i j) t := by
  let e := ordinaryChart x
  have he := (ordinaryChart_contMDiffOn x).mdifferentiableOn (by simp)
  have hei := (ordinaryChart_inverse_contMDiffOn x).mdifferentiableOn (by simp)
  have hz : chartPt x x ∈ e.source := by rw [ordinaryChart_source]; exact mem_extChartAt_target x
  have hh := flow_potential_chart_matrix_hasDerivAt α hα h U hI hU hpot hpde e he hei hz ht i j
  have hcurve : (fun s => pullbackMatrix (h s) e (chartPt x x) i j) =
      (fun s => gMat (h s) x i j) := by
    funext s
    rw [ordinaryChart_pullbackMatrix_center]
  rw [hcurve] at hh
  erw [ordinaryChart_logdet_levi (h t) x (mem_extChartAt_target x)] at hh
  convert hh using 1
  simp only [ricci, Matrix.neg_apply, neg_neg]
  rfl

end Yau.NodeProofs.F01Aux
