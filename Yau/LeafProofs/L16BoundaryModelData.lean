import Yau.LeafProofs.L16ChartLowJetTransport

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance boundaryModelData_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance boundaryModelData_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance boundaryModelData_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance boundaryModelData_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- The original smooth-domain hypothesis supplies a boundary chart on which
    the original value and original spatial gradient of every Schauder datum
    have a uniform Holder bound. Every geometric constant precedes the datum. -/
theorem smoothDomain_boundary_model_data_low_holder {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {x : Space n} (hx : x ∈ frontier O) {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
    ∃ (e : Space n) (c : OpenPartialHomeomorph (Space n) (Space n)) (q A : ℝ),
      ‖e‖ = 1 ∧ x ∈ c.source ∧ c x = 0 ∧ 0 < q ∧ 0 < A ∧
      Metric.closedBall 0 (4*q) ⊆ c.target ∧
      ContDiffOn ℝ 3 c c.source ∧ ContDiffOn ℝ 3 c.symm c.target ∧
      (∀ y ∈ c.source, (y ∈ O ↔ 0 < inner ℝ e (c y)) ∧
        (y ∈ closure O ↔ 0 ≤ inner ℝ e (c y)) ∧ (y ∈ frontier O ↔ inner ℝ e (c y) = 0)) ∧
      ∀ (u : Point n → ℝ) P, SchauderBound α (cylinder (closure O) 0 T) u P →
        HolderBound α (cylinder ({y | 0 ≤ inner ℝ e y}∩Metric.closedBall 0 (q/2)) 0 T)
          (fun p => (u (c.symm p.1,p.2),spatialD u (c.symm p.1,p.2))) (A*P) := by
  obtain ⟨e,c,he,hxc,hcx,hc,hci,hFaces⟩ := smoothDomain_boundary_closed_flat_chart hO hx
  obtain ⟨r,q,hr,hq,hSource,hTarget⟩ := openPartialHomeomorph_buffered_radii c hxc hcx
  let V := Metric.ball (0 : Space n) (3*q)
  let K := {y : Space n | 0 ≤ inner ℝ e y}∩Metric.closedBall 0 (q/2)
  have hVBall : V ⊆ Metric.closedBall 0 (4*q) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hVT : V ⊆ c.target := hVBall.trans hTarget
  have hKV : K ⊆ V := fun y hy => Metric.closedBall_subset_ball (by linarith : q/2 < 3*q) hy.2
  have hKT : K ⊆ c.target := hKV.trans hVT
  have hMapV : MapsTo c.symm ({y | 0 ≤ inner ℝ e y}∩V) (closure O) := by
    intro y hy
    apply (hFaces (c.symm y) (c.map_target (hVT hy.2))).2.1.mpr
    rw [c.right_inv (hVT hy.2)]
    exact hy.1
  have hMapK : MapsTo c.symm K (closure O) := fun y hy => hMapV ⟨hy.1,hKV hy⟩
  obtain ⟨C,hC,hChartBound⟩ := compact_actual_three_jet_bound c.open_target
    (isCompact_closedBall 0 (4*q)) hTarget hci
  have hChart : ∀ y ∈ {y | 0 ≤ inner ℝ e y}∩V,
      ‖fderiv ℝ c.symm y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ c.symm) y‖ ≤ C := by
    intro y hy
    exact ⟨(hChartBound y (hVBall hy.2)).1,(hChartBound y (hVBall hy.2)).2.1⟩
  let φ : Space n → ℝ := innerPatchBump q hq 0
  have hφ : ContDiff ℝ ∞ φ := innerPatchBump_contDiff hq 0
  have hcφ : HasCompactSupport φ := (innerPatchBump q hq 0).hasCompactSupport
  have hSupport : tsupport φ ⊆ V := by
    rw [(innerPatchBump q hq 0).tsupport_eq]
    change Metric.closedBall (0 : Space n) (3*q/2) ⊆ Metric.ball 0 (3*q)
    exact Metric.closedBall_subset_ball (by linarith)
  obtain ⟨A,hA,hLow⟩ := chart_cutoff_lowPair_holder hα hα1 hT hC.le he
    (show IsOpen V from Metric.isOpen_ball) (hci.mono hVT) hMapV hChart hφ hcφ hSupport
  have hSmallTarget : Metric.closedBall (0 : Space n) (q/2) ⊆ c.target :=
    (Metric.closedBall_subset_closedBall (by linarith : q/2 ≤ 4*q)).trans hTarget
  obtain ⟨D,hD,hJacFull⟩ := compact_chart_inverse_jacobian_holder hα hα1 c hc hci
    (isCompact_closedBall 0 (q/2)) (convex_closedBall 0 (q/2)) hSmallTarget
  have hJac : HolderBound α (cylinder K 0 T) (fun p => fderiv ℝ c (c.symm p.1)) D :=
    holderBound_mono hJacFull (fun p hp => ⟨hp.1.2,hp.2⟩)
  have hPlateau : ∀ y ∈ K, ∀ᶠ z in 𝓝 y, φ z = 1 := by
    intro y hy
    apply innerPatchBump_eventually_one_of_norm_lt hq
    rw [sub_zero]
    have hyN : ‖y‖ ≤ q/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy.2
    linarith
  refine ⟨e,c,q,A+2*A*D,he,hxc,hcx,hq,by positivity,hTarget,hc,hci,hFaces,?_⟩
  intro u P hu
  have hh := chart_lowPair_original_gradient_holder c hc hci hKT (fun y hy => hy.1) hMapK
    hPlateau hu.1 (hLow u P hu) hJac
  have hBudget : A*P+2*(A*P)*D = (A+2*A*D)*P := by ring
  rw [hBudget] at hh
  exact hh

end Yau.LeafProofs.L16Aux
