import Yau.Proofs.P02PlanarComparison

/-! The actual closed-disc maximum principle follows from interior lower
C² supports with nonnegative planar trace. No boundary extension is used. -/

noncomputable section
open scoped Topology
open Filter Metric
namespace Yau.NodeProofs.D02Aux
open Yau Yau.NodeProofs.P02Aux

theorem planar_maximum_of_lower_supports (f : ℂ → ℝ)
    (hfc : ContinuousOn f (closedBall 0 1))
    (hsupport : ∀ a ∈ ball (0 : ℂ) 1,
      ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s a ∧ s a = f a ∧
        (∀ᶠ z in 𝓝 a, s z ≤ f z) ∧ 0 ≤ planarTrace s a)
    (B : ℝ) (hboundary : ∀ z : ℂ, ‖z‖ = 1 → f z ≤ B) :
    ∀ z ∈ closedBall (0 : ℂ) 1, f z ≤ B := by
  intro z hz
  by_contra hbad
  let A := f z - B
  have hA : 0 < A := sub_pos.mpr (lt_of_not_ge hbad)
  let h : ℂ → ℝ := fun w => B + A / 2 - A / 2 * ‖w‖ ^ 2
  have hnorm : ContDiff ℝ 2 (fun w : ℂ => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  have hh (w : ℂ) : ContDiffAt ℝ 2 h w :=
    contDiffAt_const.sub (contDiffAt_const.mul hnorm.contDiffAt)
  have hposz : 0 < f z - h z := by
    dsimp only [h, A] at *
    nlinarith [sq_nonneg ‖z‖]
  have hboundary' (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 1) : f w - h w ≤ 0 := by
    have hn : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
    have hb := hboundary w hn
    dsimp only [h]
    rw [hn]
    norm_num
    linarith
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    ⟨z, hz⟩ (hfc.sub (fun w _ => (hh w).continuousAt.continuousWithinAt))
  have hpos : 0 < f a - h a := hposz.trans_le (hmax hz)
  have haB : a ∈ ball (0 : ℂ) 1 := by
    have hn : ‖a‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using ha
    have hne : ‖a‖ ≠ 1 := by
      intro he
      have hb := hboundary' a (by simpa only [mem_sphere, dist_zero_right] using he)
      linarith
    simpa only [mem_ball, dist_zero_right] using lt_of_le_of_ne hn hne
  obtain ⟨s, hs, hs0, hsbelow, hstrace⟩ := hsupport a haB
  have hmin : IsLocalMin (fun w => h w - s w) a := by
    change ∀ᶠ w in 𝓝 a, h a - s a ≤ h w - s w
    filter_upwards [hsbelow, isOpen_ball.mem_nhds haB] with w hw hwB
    have hcomp := hmax (ball_subset_closedBall hwB)
    change f w - h w ≤ f a - h a at hcomp
    rw [hs0]
    linarith
  have htrace := planarTrace_nonneg_of_localMin ((hh a).sub hs) hmin
  have hsub : (fun w => h w - s w) = fun w => h w + (-1) * s w := by funext w; ring
  rw [hsub, planarTrace_add h (fun w => (-1) * s w) a (hh a)
    (contDiffAt_const.mul hs), planarTrace_const_mul s a hs (-1)] at htrace
  have htrh : planarTrace h a = -2 * A := by
    have heq : h = fun w => (B + A / 2) + (-A / 2) * ‖w‖ ^ 2 := by funext w; dsimp [h]; ring
    rw [heq, planarTrace_add _ _ a contDiffAt_const (contDiffAt_const.mul hnorm.contDiffAt),
      planarTrace_const, planarTrace_const_mul _ a hnorm.contDiffAt, planarTrace_norm_sq]
    ring
  rw [htrh] at htrace
  linarith

end Yau.NodeProofs.D02Aux
