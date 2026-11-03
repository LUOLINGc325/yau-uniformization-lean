import Yau.Proofs.P02PoissonApproximation
import Yau.Proofs.P02PlanarTrace

noncomputable section
open Filter Metric Complex InnerProductSpace
open scoped Topology

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L22Aux

/-- The lower touching functions are genuine C² functions.  A harmonic
boundary approximation and the second derivative test prove the actual
circle inequality; no viscosity or submean oracle is an input. -/
theorem planar_submean_of_lower_supports (f : ℂ → ℝ)
    (hfc : ContinuousOn f (closedBall 0 1))
    (hsupport : ∀ a ∈ ball (0 : ℂ) 1,
      ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s a ∧ s a = f a ∧
        (∀ᶠ z in 𝓝 a, s z ≤ f z) ∧ 0 ≤ planarTrace s a) :
    f 0 ≤ Yau.circleAverage (fun θ => f (Complex.exp (θ*Complex.I))) := by
  rw [circleAverage_eq_real_circleAverage]
  by_contra hbad
  let A := f 0-Real.circleAverage f 0 1
  have hA : 0 < A := sub_pos.mpr (lt_of_not_ge hbad)
  have hFs : ContinuousOn f (sphere (0 : ℂ) 1) :=
    hfc.mono sphere_subset_closedBall
  obtain ⟨H,hH,hH0,herr⟩ := exists_harmonic_boundary_approx f hFs (A/4) (by positivity)
  let h : ℂ → ℝ := fun z => H z+A/2-A/4*‖z‖^2
  have hnorm : ContDiff ℝ 2 (fun z : ℂ => ‖z‖^2) := contDiff_norm_sq ℝ
  have hhc (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : ContDiffAt ℝ 2 h z :=
    ((hH z hz).1.add contDiffAt_const).sub (contDiffAt_const.mul hnorm.contDiffAt)
  have hHc : ContinuousOn H (closedBall (0 : ℂ) 1) :=
    fun z hz => (hH z hz).1.continuousAt.continuousWithinAt
  have hhc' : ContinuousOn h (closedBall (0 : ℂ) 1) :=
    fun z hz => (hhc z hz).continuousAt.continuousWithinAt
  have hcenter : 0 < f 0-h 0 := by
    dsimp only [h]
    rw [hH0]
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero]
    dsimp only [A] at hA ⊢
    linarith
  have hboundary (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) : f z-h z < 0 := by
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz
    have HH := (abs_lt.mp (herr z hz)).1
    dsimp only [h]
    rw [hn]
    norm_num
    linarith
  obtain ⟨a,ha,hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    (by exact ⟨0,by simp⟩) (hfc.sub hhc')
  have hpos : 0 < f a-h a := hcenter.trans_le (hmax (by simp))
  have haB : a ∈ ball (0 : ℂ) 1 := by
    have hn : ‖a‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using ha
    have hne : ‖a‖ ≠ 1 := by
      intro he
      have HH := hboundary a (by simpa only [mem_sphere,dist_zero_right] using he)
      linarith
    simpa only [mem_ball,dist_zero_right] using lt_of_le_of_ne hn hne
  obtain ⟨s,hsc,hs0,hsbelow,hstrace⟩ := hsupport a haB
  have hmin : IsLocalMin (fun z => h z-s z) a := by
    change ∀ᶠ z in 𝓝 a, h a-s a ≤ h z-s z
    filter_upwards [hsbelow,isOpen_ball.mem_nhds haB] with z hz hzB
    have HH := hmax (ball_subset_closedBall hzB)
    change f z-h z ≤ f a-h a at HH
    rw [hs0]
    linarith
  have htrace := planarTrace_nonneg_of_localMin ((hhc a ha).sub hsc) hmin
  have hsub : (fun z => h z-s z) = fun z => h z+(-1)*s z := by funext z; ring
  rw [hsub,planarTrace_add h (fun z => (-1)*s z) a (hhc a ha)
    (contDiffAt_const.mul hsc),planarTrace_const_mul s a hsc (-1)] at htrace
  have htrh : planarTrace h a = -A := by
    have heq : h = fun z => (H z+A/2)+(-A/4)*‖z‖^2 := by funext z; dsimp [h]; ring
    rw [heq,planarTrace_add _ _ a ((hH a ha).1.add contDiffAt_const)
      (contDiffAt_const.mul hnorm.contDiffAt),
      planarTrace_add H (fun _ => A/2) a (hH a ha).1 contDiffAt_const,
      planarTrace_const,planarTrace_harmonic (hH a ha),
      planarTrace_const_mul _ a hnorm.contDiffAt,planarTrace_norm_sq]
    ring
  rw [htrh] at htrace
  linarith

end Yau.NodeProofs.P02Aux
