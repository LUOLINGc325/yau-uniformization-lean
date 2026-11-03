import Yau.Proofs.F05JetCutoffContinuity
import Yau.Proofs.F05JetSpatialRealization
import Yau.Proofs.F05JetTimeRealization
import Yau.Proofs.F05ModelGeometry

/-! The cutoff expressions are the actual derivatives, first on the chart
interior and then across its artificial rim. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true

namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_cutoffDDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_cutoffDDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_cutoffDHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_cutoffDHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

theorem F05_cutoff_jet_zero {α : ℝ} {Q : Set (Point n)}
    (φ : Space n → ℝ) (u : F05JetComponent α Q) {p : Point n}
    (hp : p.1 ∉ tsupport φ) :
    F05CutoffJetValue φ u p = 0 ∧ F05CutoffJetGradient φ u p = 0 ∧
      F05CutoffJetHessian φ u p = 0 ∧ F05CutoffJetTime φ u p = 0 := by
  have hφ : φ p.1 = 0 := image_eq_zero_of_notMem_tsupport hp
  have hD : fderiv ℝ φ p.1 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (tsupport_fderiv_subset ℝ h))
  have hDD : fderiv ℝ (fderiv ℝ φ) p.1 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ h)))
  simp only [F05CutoffJetValue,F05CutoffJetGradient,F05CutoffJetHessian,
    F05CutoffJetTime,hφ,hD,hDD,zero_mul,zero_smul,smul_zero,zero_add,
    ContinuousLinearMap.zero_smulRight,ContinuousLinearMap.smulRight_zero,and_self]

theorem F05_cutoff_jet_derivatives_interior (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ) (t : Icc 0 T)
    {z : Space n} (hz : z ∈ interior (F05D A i)) :
    HasFDerivAt (fun w => F05CutoffJetValue φ u.val (w,t.val))
      (F05CutoffJetGradient φ u.val (z,t.val)) z ∧
    HasFDerivAt (fun w => F05CutoffJetGradient φ u.val (w,t.val))
      (F05CutoffJetHessian φ u.val (z,t.val)) z := by
  have hV := F05LocalFTCGraph_hasFDerivAt_value A i α hT u t hz
  have hG := F05LocalFTCGraph_hasFDerivAt_gradient A i α hT u t hz
  rw [← F05BCFFun_apply u.val.2.1 ⟨(z,t.val),interior_subset hz,t.property⟩] at hV
  rw [← F05BCFFun_apply u.val.2.2.1.val.1
    ⟨(z,t.val),interior_subset hz,t.property⟩] at hG
  have hφD : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hDφ := (hφ.differentiable (by simp) z).hasFDerivAt
  have hDDφ := (hφD.differentiable (by simp) z).hasFDerivAt
  constructor
  · exact hDφ.mul hV
  · have hh := (hDφ.smul hG).add (hV.smul hDDφ)
    apply hh.congr_fderiv
    ext a b
    simp only [F05CutoffJetHessian,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul]
    ring

theorem F05_cutoff_jet_derivatives_model (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hSupport : tsupport φ ⊆ Metric.closedBall 0 1)
    {p : Point n} (hp : p ∈ cylinder (F05ModelOpen A i) 0 T) :
    HasFDerivAt (fun w => F05CutoffJetValue φ u.val (w,p.2))
      (F05CutoffJetGradient φ u.val p) p.1 ∧
    HasFDerivAt (fun w => F05CutoffJetGradient φ u.val (w,p.2))
      (F05CutoffJetHessian φ u.val p) p.1 := by
  by_cases hn : ‖p.1‖ < 2
  · exact F05_cutoff_jet_derivatives_interior A i α hT u φ hφ ⟨p.2,hp.2⟩
      (F05D_interior_of_model A i hp.1 hn)
  · have hOut : p.1 ∉ tsupport φ := by
      intro h
      have hb := hSupport h
      have hb' : ‖p.1‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hb
      exact hn (hb'.trans_lt (by norm_num))
    have hNear : ∀ᶠ w in 𝓝 p.1, w ∉ tsupport φ :=
      (isClosed_tsupport φ).isOpen_compl.mem_nhds hOut
    have hV : (fun w => F05CutoffJetValue φ u.val (w,p.2)) =ᶠ[𝓝 p.1] (fun _ => 0) :=
      hNear.mono fun w hw => (F05_cutoff_jet_zero φ u.val hw).1
    have hG : (fun w => F05CutoffJetGradient φ u.val (w,p.2)) =ᶠ[𝓝 p.1] (fun _ => 0) :=
      hNear.mono fun w hw => (F05_cutoff_jet_zero φ u.val hw).2.1
    rw [(F05_cutoff_jet_zero φ u.val hOut).2.1,(F05_cutoff_jet_zero φ u.val hOut).2.2.1]
    exact ⟨(hasFDerivAt_const (0 : ℝ) p.1).congr_of_eventuallyEq hV,
      (hasFDerivAt_const (0 : F05Dual n) p.1).congr_of_eventuallyEq hG⟩

theorem F05_cutoff_jet_time_model (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (φ : Space n → ℝ) (hSupport : tsupport φ ⊆ Metric.closedBall 0 1)
    {p : Point n} (hp : p ∈ cylinder (closure (F05ModelOpen A i)) 0 T) :
    HasDerivWithinAt (fun r => F05CutoffJetValue φ u.val (p.1,r))
      (F05CutoffJetTime φ u.val p) (Icc 0 T) p.2 := by
  by_cases hD : p.1 ∈ F05D A i
  · exact (F05LocalFTCGraph_hasDerivWithinAt_raw_time A i α hT u hD hp.2).const_mul (φ p.1)
  · have hOut : p.1 ∉ tsupport φ := by
      intro h
      have hb := hSupport h
      have hb' : ‖p.1‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hb
      apply hD
      have hFace := hp.1
      rw [F05ModelOpen_eq,F05FlatOpen_closure] at hFace
      exact ⟨hb'.trans (by norm_num),hFace⟩
    have hz := image_eq_zero_of_notMem_tsupport hOut
    simpa only [F05CutoffJetValue,F05CutoffJetTime,hz,zero_mul] using
      (hasDerivWithinAt_const p.2 (Icc 0 T) (0 : ℝ))

end Yau.Proofs.F05Aux
