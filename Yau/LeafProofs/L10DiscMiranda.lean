import Yau.LeafProofs.L10DiscMirandaBoundary

/-! The literal real-valued disc Miranda--Talenti estimate, with all
closed-boundary derivatives taken within the disc. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs

theorem discMirandaTalenti_identity {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      (discEnergyPartial (discEnergyPartial u 1) 1 z +
        discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z)^2 -
      ((discEnergyPartial (discEnergyPartial u 1) 1 z)^2 +
        (discEnergyPartial (discEnergyPartial u 1) Complex.I z)^2 +
        (discEnergyPartial (discEnergyPartial u Complex.I) 1 z)^2 +
        (discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z)^2)) =
      ∫ θ in (-Real.pi)..Real.pi,
        ((L08_unitCircle θ).re * discEnergyPartial u 1 (L08_unitCircle θ) +
          (L08_unitCircle θ).im * discEnergyPartial u Complex.I (L08_unitCircle θ))^2 := by
  calc
    _ = ∫ z in Metric.ball (0 : ℂ) 1,
        (fderiv ℝ (discMirandaFlux u) z 1).re + (fderiv ℝ (discMirandaFlux u) z Complex.I).im := by
      exact setIntegral_congr_fun measurableSet_ball
        (fun z hz => (discMirandaFlux_divergence hu hz).symm)
    _ = ∫ θ in (-Real.pi)..Real.pi,
        inner ℝ (L08_unitCircle θ) (discMirandaFlux u (L08_unitCircle θ)) :=
      discEnergy_integral_divergence_smooth (discMirandaFlux_contDiffOn hu)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact discMirandaFlux_circle hu hzero θ

theorem discMirandaTalenti {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      (discEnergyPartial (discEnergyPartial u 1) 1 z)^2 +
      (discEnergyPartial (discEnergyPartial u 1) Complex.I z)^2 +
      (discEnergyPartial (discEnergyPartial u Complex.I) 1 z)^2 +
      (discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z)^2) ≤
    ∫ z in Metric.ball (0 : ℂ) 1,
      (discEnergyPartial (discEnergyPartial u 1) 1 z +
        discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z)^2 := by
  let a := discEnergyPartial (discEnergyPartial u 1) 1
  let b := discEnergyPartial (discEnergyPartial u 1) Complex.I
  let c := discEnergyPartial (discEnergyPartial u Complex.I) 1
  let d := discEnergyPartial (discEnergyPartial u Complex.I) Complex.I
  have hp := discEnergyPartial_contDiffOn hu (1 : ℂ)
  have hq := discEnergyPartial_contDiffOn hu Complex.I
  have ha : ContinuousOn a (Metric.closedBall (0 : ℂ) 1) :=
    (discEnergyPartial_contDiffOn hp (1 : ℂ)).continuousOn
  have hb : ContinuousOn b (Metric.closedBall (0 : ℂ) 1) :=
    (discEnergyPartial_contDiffOn hp Complex.I).continuousOn
  have hc : ContinuousOn c (Metric.closedBall (0 : ℂ) 1) :=
    (discEnergyPartial_contDiffOn hq (1 : ℂ)).continuousOn
  have hd : ContinuousOn d (Metric.closedBall (0 : ℂ) 1) :=
    (discEnergyPartial_contDiffOn hq Complex.I).continuousOn
  have htrace : IntegrableOn (fun z => (a z + d z)^2) (Metric.ball (0 : ℂ) 1) volume :=
    (((ha.add hd).pow 2).integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  have hHS : IntegrableOn (fun z => a z ^ 2 + b z ^ 2 + c z ^ 2 + d z ^ 2)
      (Metric.ball (0 : ℂ) 1) volume :=
    (((((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)).add (hd.pow 2)).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall
  have hi := discMirandaTalenti_identity hu hzero
  change (∫ z in Metric.ball (0 : ℂ) 1,
      (a z + d z)^2 - (a z ^ 2 + b z ^ 2 + c z ^ 2 + d z ^ 2)) = _ at hi
  rw [integral_sub htrace hHS] at hi
  have hn : 0 ≤ ∫ θ in (-Real.pi)..Real.pi,
      ((L08_unitCircle θ).re * discEnergyPartial u 1 (L08_unitCircle θ) +
        (L08_unitCircle θ).im * discEnergyPartial u Complex.I (L08_unitCircle θ))^2 := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith [Real.pi_pos])
    intro θ
    exact sq_nonneg _
  change (∫ z in Metric.ball (0 : ℂ) 1, a z ^ 2 + b z ^ 2 + c z ^ 2 + d z ^ 2) ≤
    ∫ z in Metric.ball (0 : ℂ) 1, (a z + d z)^2
  linarith

end Yau.LeafProofs
