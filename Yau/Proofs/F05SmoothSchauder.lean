import Yau.Proofs.F05SmoothLaplacian
import Yau.Proofs.F05SmoothSlices
import Yau.Proofs.F05FixedZeroSource

/-! Actual smooth backgrounds have a fixed full parabolic Schauder budget
before the exponent and the moving endpoint, with their literal time jet. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}
local instance f05_smoothHessianGroup : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance f05_smoothHessianSpace : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

theorem F05_timeD_smooth_restrict {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {p : M.Carrier → ℝ → ℝ} {S T : ℝ}
    (hp : SmoothSpaceTime p (Icc 0 S)) (hT : 0 < T) (hTS : T ≤ S)
    (i : Fin A.count) {q : Point n} (hq : q ∈ F05Q A i T) :
    timeD (F05Q A i T) (pull A i p) q = derivWithin (p (lift A i q.1)) (Icc 0 S) q.2 := by
  exact (F05_timeD_pull A i T p (p := q) hq.1).trans
    (F05_derivWithin_Icc_restrict hT hTS hq.2
      ((F05_smooth_time_slice hp _).differentiableOn (by simp) q.2 ⟨hq.2.1,hq.2.2.trans hTS⟩))

theorem F05_smooth_chart_schauder_budget {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (p : M.Carrier → ℝ → ℝ) {S : ℝ}
    (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S)) (i : Fin A.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ), 0 < T → T ≤ S →
      SchauderBound α (F05Q A i T) (pull A i p) C := by
  have hφ := F05_pull_spacetime_smooth hA p hp i
  have hJets := F05_joint_spatial_jets_smooth Metric.isOpen_ball hφ
  have hTime := F05_joint_time_derivative_smooth (uniqueDiffOn_Icc hS) hφ
  have hKU : Metric.closedBall (0 : Space n) 2 ⊆ Metric.ball 0 3 := Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨C₀,hC₀,hValue⟩ := F05_compact_cylinder_holder Metric.isOpen_ball (isCompact_closedBall (0 : Space n) 2)
    (convex_closedBall (0 : Space n) 2) hKU hS hφ
  obtain ⟨C₁,hC₁,hGradient⟩ := F05_compact_cylinder_holder Metric.isOpen_ball (isCompact_closedBall (0 : Space n) 2)
    (convex_closedBall (0 : Space n) 2) hKU hS hJets.1
  obtain ⟨C₂,hC₂,hHessian⟩ := F05_compact_cylinder_holder Metric.isOpen_ball (isCompact_closedBall (0 : Space n) 2)
    (convex_closedBall (0 : Space n) 2) hKU hS hJets.2
  obtain ⟨C₃,hC₃,hTimeBound⟩ := F05_compact_cylinder_holder Metric.isOpen_ball (isCompact_closedBall (0 : Space n) 2)
    (convex_closedBall (0 : Space n) 2) hKU hS hTime
  let C := C₀+C₁+C₂+C₃
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro α hα hα1 T hT hTS
  have hSub : F05Q A i T ⊆ cylinder (Metric.closedBall 0 2) 0 T := fun q hq =>
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hq.1.1,hq.2⟩
  have hV := holderBound_mono (hValue α hα hα1 T hTS) hSub
  have hG := holderBound_mono (hGradient α hα hα1 T hTS) hSub
  have hH := holderBound_mono (hHessian α hα hα1 T hTS) hSub
  have hTraw := holderBound_mono (hTimeBound α hα hα1 T hTS) hSub
  have hTact := holderBound_congr_on hTraw (fun q hq => (F05_timeD_smooth_restrict hA hp hT hTS i hq).symm)
  refine ⟨F05_smooth_actual_chart_c2 hA hp hT hTS i,hC.le,?_,?_,?_⟩
  · intro q hq
    exact ⟨(hV.2.1 q hq).trans (by dsimp only [C]; linarith),
      (hG.2.1 q hq).trans (by dsimp only [C]; linarith)⟩
  · exact holderBound_mono_const hH (by dsimp only [C]; linarith)
  · exact holderBound_mono_const hTact (by dsimp only [C]; linarith)

theorem F05_smooth_schauder_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (p : M.Carrier → ℝ → ℝ) {S : ℝ}
    (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ), 0 < T → T ≤ S →
      ∀ i, SchauderBound α (F05Q A i T) (pull A i p) C := by
  classical
  choose B hB hBudget using (fun i : Fin A.count => F05_smooth_chart_schauder_budget hA p hS hp i)
  let C := 1+∑ i,B i
  have hSum : 0 ≤ ∑ i,B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro α hα hα1 T hT hTS i
  apply schauderBound_mono_const (hBudget i α hα hα1 T hT hTS)
  have hSingle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hB j).le)
    (Finset.mem_univ i)
  dsimp only [C]
  linarith

end Yau.Proofs.F05Aux
