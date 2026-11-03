import Yau.Blueprint.ParabolicSpaces
import Yau.LeafProofs.L17SchauderSpaceFTC

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem auto_segment_integrable {O : Set E} {J : E → E →L[ℝ] F}
    (hJ : ContinuousOn J O) (x h : E)
    (hpath : ∀ s∈Icc (0 : ℝ) 1, x+s • h∈O) :
    IntervalIntegrable (fun s : ℝ => J (x+s • h) h) volume 0 1 := by
  have hp : Continuous (fun s : ℝ => x+s • h) := continuous_const.add (continuous_id.smul continuous_const)
  have hC := (hJ.comp hp.continuousOn hpath).clm_apply (continuousOn_const (c := h))
  have hC' : ContinuousOn (fun s : ℝ => J (x+s • h) h) (Icc (0 : ℝ) 1) := by
    convert! hC using 1
  exact (show ContinuousOn (fun s : ℝ => J (x+s • h) h) (uIcc (0 : ℝ) 1) by
    simpa only [uIcc_of_le zero_le_one] using hC').intervalIntegrable

theorem auto_hasFDerivAt_from_segment_integral {O : Set E} (hO : IsOpen O)
    {f : E → F} {J : E → E →L[ℝ] F} (hJ : ContinuousOn J O)
    (hFTC : ∀ x∈O, ∀ h : E, (∀ s∈Icc (0 : ℝ) 1, x+s • h∈O) →
      f (x+h)-f x=∫ s in (0 : ℝ)..1, J (x+s • h) h) :
    ∀ x∈O, HasFDerivAt f (J x) x := by
  intro x hx
  obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hO x hx
  apply Yau.LeafProofs.L17SchauderAux.hasFDerivAt_of_segment_integral isOpen_ball (convex_ball x r)
    (hJ.mono hBall) ?_ (mem_ball_self hr)
  intro a ha b hb
  have hpath : ∀ s∈Icc (0 : ℝ) 1, a+s • (b-a)∈O := by
    intro s hs
    apply hBall
    have h := (convex_ball x r).lineMap_mem ha hb hs
    simpa only [AffineMap.lineMap_apply_module',add_comm] using h
  have h := hFTC a (hBall ha) (b-a) hpath
  rw [show a+(b-a)=b by abel] at h
  simpa only [AffineMap.lineMap_apply_module',add_comm] using h

theorem auto_scalar_from_segment_integral {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {f : Space n → ℝ} {G : Space n → Space n →L[ℝ] ℝ} (hG : ContinuousOn G O)
    (hFTC : ∀ x∈O, ∀ h : Space n, (∀ s∈Icc (0 : ℝ) 1, x+s • h∈O) →
      f (x+h)-f x=∫ s in (0 : ℝ)..1, G (x+s • h) h) :
    ∀ x∈O, HasFDerivAt f (G x) x :=
  auto_hasFDerivAt_from_segment_integral hO hG hFTC

theorem auto_gradient_from_segment_integral {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {g : Space n → Space n →L[ℝ] ℝ}
    {B : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ} (hB : ContinuousOn B O)
    (hFTC : ∀ x∈O, ∀ h : Space n, (∀ s∈Icc (0 : ℝ) 1, x+s • h∈O) →
      g (x+h)-g x=∫ s in (0 : ℝ)..1, B (x+s • h) h) :
    ∀ x∈O, HasFDerivAt g (B x) x :=
  auto_hasFDerivAt_from_segment_integral hO hB hFTC

theorem auto_contDiffAt_two_of_actual_derivatives {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {f : Space n → ℝ} {G : Space n → Space n →L[ℝ] ℝ}
    {B : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hB : ContinuousOn B O) (hDG : ∀ x∈O, HasFDerivAt G (B x) x)
    (hDf : ∀ x∈O, HasFDerivAt f (G x) x) : ∀ x∈O, ContDiffAt ℝ 2 f x := by
  intro x hx
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨G,⟨O,hO.mem_nhds hx,hDf⟩,?_⟩
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
  refine ⟨B,⟨O,hO.mem_nhds hx,hDG⟩,?_⟩
  exact contDiffAt_zero.mpr ⟨O,hO.mem_nhds hx,hB⟩

theorem auto_second_derivative_of_actual_derivatives {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {f : Space n → ℝ} {G : Space n → Space n →L[ℝ] ℝ}
    {B : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hDG : ∀ x∈O, HasFDerivAt G (B x) x) (hDf : ∀ x∈O, HasFDerivAt f (G x) x) :
    ∀ x∈O, fderiv ℝ (fderiv ℝ f) x=B x := by
  intro x hx
  have hEq : fderiv ℝ f=ᶠ[𝓝 x] G := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact (hDf y hy).fderiv
  exact hEq.fderiv_eq.trans (hDG x hx).fderiv

end Yau.LeafProofs.L05AutonomousAux
