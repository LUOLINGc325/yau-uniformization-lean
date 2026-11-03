import Yau.Proofs.V02DiscTraceFull

/-! The same canonical dbar solution preserves addition and antisymmetry.
Only the actual density on the closed disc is relevant to its Green integral. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.LeafProofs

theorem discGreenSolution_congr_closed {b c : ℂ → ℂ}
    (hbc : Set.EqOn b c (Metric.closedBall (0 : ℂ) 1)) :
    discGreenSolution b = discGreenSolution c := by
  funext z
  unfold discGreenSolution
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro w hw
  dsimp only
  rw [hbc (Metric.ball_subset_closedBall hw)]

theorem discDbarSolution_congr_closed {b c : ℂ → ℂ}
    (hbc : Set.EqOn b c (Metric.closedBall (0 : ℂ) 1)) :
    discDbarSolution b = discDbarSolution c := by
  unfold discDbarSolution
  rw [discGreenSolution_congr_closed hbc]

theorem discDbarSolution_add {b c : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1))
    (hc : ContDiffOn ℝ ∞ c (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discDbarSolution (b + c) z = discDbarSolution b z + discDbarSolution c z := by
  have hu := discGreenSolution_contDiffOn hb
  have hv := discGreenSolution_contDiffOn hc
  have he : Set.EqOn (discGreenSolution (b + c))
      (fun w => discGreenSolution b w + discGreenSolution c w) (Metric.closedBall (0 : ℂ) 1) :=
    fun _ hw => discGreenSolution_add hb.continuousOn hc.continuousOn hw
  have hp (a : ℂ) : discEnergyPartial (discGreenSolution (b + c)) a z =
      discEnergyPartial (discGreenSolution b) a z + discEnergyPartial (discGreenSolution c) a z := by
    unfold discEnergyPartial
    rw [fderivWithin_congr' he hz, fderivWithin_fun_add (disc_closedBall_uniqueDiffOn z hz)
      ((hu.differentiableOn (by simp)) z hz) ((hv.differentiableOn (by simp)) z hz)]
    rfl
  simp only [discDbarSolution, hp]
  ring

theorem discDbarSolution_skew {ι : Type*} (b : ι → ι → ℂ → ℂ)
    (hb : ∀ i j, ContDiffOn ℝ ∞ (b i j) (Metric.closedBall (0 : ℂ) 1))
    (hskew : ∀ i j z, z ∈ Metric.closedBall (0 : ℂ) 1 → b i j z = -b j i z)
    (i j : ι) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discDbarSolution (b i j) z = -discDbarSolution (b j i) z := by
  have he : Set.EqOn (b i j) (-(b j i)) (Metric.closedBall (0 : ℂ) 1) :=
    fun w hw => hskew i j w hw
  rw [discDbarSolution_congr_closed he]
  exact discDbarSolution_neg (hb j i) hz

end Yau.Blueprint.V02Proof
