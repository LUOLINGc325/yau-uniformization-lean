import Yau.Proofs.C03EnvelopeSmoothingPlanar
import Yau.Proofs.C03EnvelopeSmoothingExtension

/-! A frozen scalar quadratic is subtracted from genuine planar touching germs. -/
noncomputable section
open scoped Topology ContDiff
open Filter Metric Set
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau Yau.LeafProofs L22Aux Yau.NodeProofs.P02Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem corrected_planar_submean (F : ℂ → ℝ) (A : ℝ)
    (hFc : ContinuousOn F (closedBall 0 1))
    (hsupport : ∀ a ∈ ball (0 : ℂ) 1,
      ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s 0 ∧ s 0 = F a ∧
        (∀ᶠ b in 𝓝 0, s b ≤ F (a + b)) ∧ 4 * A ≤ planarTrace s 0) :
    F 0 + A ≤ circleAverage (fun θ => F (Complex.exp (θ * Complex.I))) := by
  let q : ℂ → ℝ := fun a => F a + (-A) * ‖a‖ ^ 2
  have hnorm : ContDiff ℝ 2 (fun a : ℂ => ‖a‖ ^ 2) := contDiff_norm_sq ℝ
  have hqc : ContinuousOn q (closedBall 0 1) :=
    hFc.add (continuousOn_const.mul hnorm.continuous.continuousOn)
  have hmean := planar_submean_of_lower_supports q hqc (fun a ha => by
    obtain ⟨s, hs, hs0, hsnear, htrace⟩ := hsupport a ha
    have hs' : ContDiffAt ℝ 2 s (a - a) := by simpa only [sub_self] using hs
    have hshift : ContDiffAt ℝ 2 (fun b : ℂ => s (b - a)) a :=
      hs'.comp (f := fun b : ℂ => b - a) a (contDiffAt_id.sub contDiffAt_const)
    have ht : Tendsto (fun b : ℂ => b - a) (𝓝 a) (𝓝 0) := by
      have hc : Continuous (fun b : ℂ => b - a) := continuous_id.sub continuous_const
      simpa only [ContinuousAt, sub_self] using hc.continuousAt (x := a)
    refine ⟨fun b => s (b - a) + (-A) * ‖b‖ ^ 2,
      hshift.add (contDiffAt_const.mul hnorm.contDiffAt), ?_, ?_, ?_⟩
    · simp only [sub_self, hs0, q]
    · filter_upwards [ht.eventually hsnear] with b hb
      have heq : a + (b - a) = b := by abel
      rw [heq] at hb
      change s (b - a) + (-A) * ‖b‖ ^ 2 ≤ F b + (-A) * ‖b‖ ^ 2
      exact add_le_add hb le_rfl
    · rw [planarTrace_add _ _ a hshift (contDiffAt_const.mul hnorm.contDiffAt),
        planarTrace_sub_const, sub_self,
        planarTrace_const_mul _ a hnorm.contDiffAt (-A), planarTrace_norm_sq]
      linarith)
  have hpath : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I)) := by fun_prop
  have hcircle : Continuous (fun θ : ℝ => F (Complex.exp (θ * Complex.I))) :=
    hFc.comp_continuous hpath (fun θ => by simp)
  have heq : (fun θ : ℝ => q (Complex.exp (θ * Complex.I))) =
      (fun θ : ℝ => F (Complex.exp (θ * Complex.I)) + (-A)) := by
    funext θ
    simp [q]
  rw [heq, circleAverage_add hcircle continuous_const, circleAverage_const] at hmean
  have hq0 : q 0 = F 0 := by simp [q]
  rw [hq0] at hmean
  linarith

theorem corrected_affine_circle {n : ℕ} (S : Set (ComplexVector n))
    (f : ComplexVector n → ℝ) (hfc : ContinuousOn f S)
    (B : ComplexVector n → ComplexVector n → ℝ)
    (hsupport : PlanarLowerSupports f S B)
    (z w : ComplexVector n) (A : ℝ)
    (hdisc : ∀ a : ℂ, ‖a‖ ≤ 1 → z + a • w ∈ S)
    (hbound : ∀ a ∈ ball (0 : ℂ) 1, 4 * A ≤ B (z + a • w) w) :
    f z + A ≤ circleAverage (fun θ => f (z + Complex.exp (θ * Complex.I) • w)) := by
  let F : ℂ → ℝ := fun a => f (z + a • w)
  have hFc : ContinuousOn F (closedBall 0 1) :=
    hfc.comp (continuous_complex_affine z w).continuousOn
      (fun a ha => hdisc a (by simpa only [mem_closedBall, dist_zero_right] using ha))
  have hmean := corrected_planar_submean F A hFc (fun a ha => by
    have ha' : ‖a‖ < 1 := by simpa only [mem_ball, dist_zero_right] using ha
    obtain ⟨s, hsc, hs0, hsnear, hstrace⟩ := hsupport (z + a • w) (hdisc a ha'.le) w
    refine ⟨s, hsc, hs0, ?_, (hbound a ha).trans hstrace⟩
    filter_upwards [hsnear] with b hb
    change s b ≤ f (z + (a + b) • w)
    have heq : (z + a • w) + b • w = z + (a + b) • w := by
      rw [add_smul]
      abel
    rwa [heq] at hb)
  simpa only [F, zero_smul, add_zero] using hmean

end Yau.Proofs.C03Aux.EnvelopeSmoothing

