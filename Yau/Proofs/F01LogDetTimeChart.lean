import Yau.Proofs.F01LogDetRatioSmooth
import Yau.Proofs.F01ClosedTimeDerivative
import Yau.Proofs.F01ClosedRicciFamily

/-! The actual one-sided derivative of the global determinant quotient
is jointly smooth and equals the actual derivative of a fixed-chart logdet.
The background determinant is independent of time and is differentiated. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def flowLogDetTime (α : HermitianField M) (h : ℝ → HermitianField M)
    (I : Set ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  derivWithin (flowLogDetRatio α h x) I t

theorem flowLogDetTime_smoothSpaceTime (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) {I : Set ℝ} (hI : UniqueDiffOn ℝ I)
    (hh : MetricFamilySmooth h I) : SmoothSpaceTime (flowLogDetTime α h I) I :=
  smoothSpaceTime_time_derivWithin (flowLogDetRatio_smoothSpaceTime α hα h hh) hI

theorem flowLogDetTime_chart_eq (α : HermitianField M)
    (h : ℝ → HermitianField M) {I : Set ℝ} (hI : UniqueDiffOn ℝ I)
    (hh : MetricFamilySmooth h I) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) {t : ℝ} (ht : t ∈ I) :
    flowLogDetTime α h I (chartInv a z) t =
      derivWithin (fun s => logDet (h s) a z) I t := by
  have hcurve : ContDiffOn ℝ ∞ (fun s => logDet (h s) a z) I :=
    (metricFamily_logDet_joint_smooth h hh a).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => ⟨hz, hs⟩)
  have heq : flowLogDetRatio α h (chartInv a z) =
      fun s => logDet (h s) a z - logDet α a z := by
    funext s
    rw [flowLogDetRatio_chart_eq α h a hz s]
    exact Real.log_div (Yau.LeafProofs.L12Aux.hMat_det_re_pos (h s) a hz).ne'
      (Yau.LeafProofs.L12Aux.hMat_det_re_pos α a hz).ne'
  have hd := ((hcurve t ht).differentiableWithinAt (by simp)).hasDerivWithinAt.sub_const
    (logDet α a z)
  unfold flowLogDetTime
  rw [heq]
  exact hd.derivWithin (hI t ht)

end Yau.NodeProofs.F01Aux
