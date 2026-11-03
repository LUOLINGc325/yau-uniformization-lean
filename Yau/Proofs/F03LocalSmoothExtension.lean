import Yau.LeafProofs.L18

/-! Genuine compact smooth extensions of local chart functions near a point. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem contDiff_mul_of_tsupport_subset {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E} (hV : IsOpen V)
    {f χ : E → ℝ} (hf : ContDiffOn ℝ ∞ f V) (hχ : ContDiff ℝ ∞ χ)
    (hχV : tsupport χ ⊆ V) : ContDiff ℝ ∞ (fun x => χ x*f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hV.mem_nhds (hχV hx)))
  · have hEq : (fun y => χ y*f y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hEq

theorem exists_local_smooth_compact_extension {n : ℕ} {M : ComplexManifold n}
    (a : M.Carrier) {V : Set (ComplexVector n)} (hV : IsOpen V)
    (hVt : V ⊆ chartTarget a) {z₀ : ComplexVector n} (hz₀ : z₀ ∈ V)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f V) :
    ∃ (F : M.Carrier → ℝ) (W : Set (ComplexVector n)),
      SmoothFn F ∧ HasCompactSupport F ∧ IsOpen W ∧ z₀ ∈ W ∧ closure W ⊆ V ∧
      ∀ z ∈ W, F (chartInv a z)=f z := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hV z₀ hz₀
  let χ : ContDiffBump z₀ := ⟨ε/4,ε/2,by positivity,by linarith only [hε]⟩
  have hχV : tsupport (χ : ComplexVector n → ℝ) ⊆ V := by
    rw [χ.tsupport_eq]
    intro z hz
    apply hball
    exact (Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hε)
  let η : ComplexVector n → ℝ := fun z => χ z*f z
  have hη : ContDiff ℝ ∞ η := contDiff_mul_of_tsupport_subset hV hf χ.contDiff hχV
  have hcη : HasCompactSupport η := χ.hasCompactSupport.mul_right
  have hηt : tsupport η ⊆ chartTarget a := tsupport_mul_subset_left.trans (hχV.trans hVt)
  let W := Metric.ball z₀ (ε/4)
  have hWV : closure W ⊆ V := by
    apply Metric.closure_ball_subset_closedBall.trans
    intro z hz
    apply hχV
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_closedBall (by dsimp only [χ];linarith only [hε]) hz
  refine ⟨chartPushforwardZero a η,W,smoothFn_chartPushforwardZero a hη hcη hηt,
    (chartPushforwardZero_properties a hη hcη hηt).1,Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity),hWV,?_⟩
  intro z hz
  rw [chartPushforwardZero_chartInv a η (hVt (hWV (subset_closure hz)))]
  change χ z*f z=f z
  rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz),one_mul]

end Yau.Proofs.F03Aux
