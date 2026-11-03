import Yau.LeafProofs.L10DiscMirandaCalculus

/-! The computed cofactor-Hessian flux and its exact divergence. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs

def discMirandaFluxRe (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z * discEnergyPartial u 1 z -
    discEnergyPartial (discEnergyPartial u 1) Complex.I z * discEnergyPartial u Complex.I z

def discMirandaFluxIm (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  discEnergyPartial (discEnergyPartial u 1) 1 z * discEnergyPartial u Complex.I z -
    discEnergyPartial (discEnergyPartial u Complex.I) 1 z * discEnergyPartial u 1 z

def discMirandaFlux (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  (discMirandaFluxRe u z : ℂ) + Complex.I * (discMirandaFluxIm u z : ℂ)

theorem discMirandaFlux_contDiffOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discMirandaFlux u) (Metric.closedBall (0 : ℂ) 1) := by
  have hp := discEnergyPartial_contDiffOn hu (1 : ℂ)
  have hq := discEnergyPartial_contDiffOn hu Complex.I
  have hR : ContDiffOn ℝ ∞ (discMirandaFluxRe u) (Metric.closedBall (0 : ℂ) 1) :=
    ((discEnergyPartial_contDiffOn hq Complex.I).mul hp).sub
      ((discEnergyPartial_contDiffOn hp Complex.I).mul hq)
  have hI : ContDiffOn ℝ ∞ (discMirandaFluxIm u) (Metric.closedBall (0 : ℂ) 1) :=
    ((discEnergyPartial_contDiffOn hp (1 : ℂ)).mul hq).sub
      ((discEnergyPartial_contDiffOn hq (1 : ℂ)).mul hp)
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hR).add
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hI))

theorem discMirandaFlux_divergence {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (fderiv ℝ (discMirandaFlux u) z 1).re + (fderiv ℝ (discMirandaFlux u) z Complex.I).im =
      (discEnergyPartial (discEnergyPartial u 1) 1 z +
        discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z)^2 -
      ((discEnergyPartial (discEnergyPartial u 1) 1 z)^2 +
        (discEnergyPartial (discEnergyPartial u 1) Complex.I z)^2 +
        (discEnergyPartial (discEnergyPartial u Complex.I) 1 z)^2 +
        (discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z)^2) := by
  have hzK := Metric.ball_subset_closedBall hz
  have hX := discMirandaFlux_contDiffOn hu
  have hR := discMiranda_partial_clm hX Complex.reCLM 1 hzK
  have hI := discMiranda_partial_clm hX Complex.imCLM Complex.I hzK
  have heR : Complex.reCLM ∘ discMirandaFlux u = discMirandaFluxRe u := by
    funext w
    simp [discMirandaFlux]
  have heI : Complex.imCLM ∘ discMirandaFlux u = discMirandaFluxIm u := by
    funext w
    simp [discMirandaFlux]
  rw [heR] at hR
  rw [heI] at hI
  change discEnergyPartial (discMirandaFluxRe u) 1 z =
    (discEnergyPartial (discMirandaFlux u) 1 z).re at hR
  change discEnergyPartial (discMirandaFluxIm u) Complex.I z =
    (discEnergyPartial (discMirandaFlux u) Complex.I z).im at hI
  rw [← discEnergyPartial_eq_fderiv (discMirandaFlux u) 1 hz,
    ← discEnergyPartial_eq_fderiv (discMirandaFlux u) Complex.I hz, ← hR, ← hI]
  let p := discEnergyPartial u 1
  let q := discEnergyPartial u Complex.I
  let a := discEnergyPartial p 1
  let b := discEnergyPartial p Complex.I
  let c := discEnergyPartial q 1
  let d := discEnergyPartial q Complex.I
  have hp : ContDiffOn ℝ ∞ p (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hu 1
  have hq : ContDiffOn ℝ ∞ q (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hu Complex.I
  have ha : ContDiffOn ℝ ∞ a (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hp 1
  have hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hp Complex.I
  have hc : ContDiffOn ℝ ∞ c (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hq 1
  have hd : ContDiffOn ℝ ∞ d (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hq Complex.I
  change discEnergyPartial (d * p - b * q) 1 z +
    discEnergyPartial (a * q - c * p) Complex.I z =
      (a z + d z)^2 - (a z ^ 2 + b z ^ 2 + c z ^ 2 + d z ^ 2)
  rw [discMiranda_partial_sub (a := d * p) (b := b * q) (hd.mul hp) (hb.mul hq) 1 hzK,
    discMiranda_partial_sub (a := a * q) (b := c * p) (ha.mul hq) (hc.mul hp) Complex.I hzK,
    discMiranda_partial_mul hd hp 1 hzK, discMiranda_partial_mul hb hq 1 hzK,
    discMiranda_partial_mul ha hq Complex.I hzK, discMiranda_partial_mul hc hp Complex.I hzK]
  have hthird1 : discEnergyPartial d 1 z = discEnergyPartial c Complex.I z :=
    discMiranda_partial_commute hq Complex.I 1 hzK
  have hthird2 : discEnergyPartial b 1 z = discEnergyPartial a Complex.I z :=
    discMiranda_partial_commute hp Complex.I 1 hzK
  have hmix : b z = c z := discMiranda_partial_commute hu 1 Complex.I hzK
  change discEnergyPartial d 1 z * p z + d z * a z -
      (discEnergyPartial b 1 z * q z + b z * c z) +
      (discEnergyPartial a Complex.I z * q z + a z * d z -
        (discEnergyPartial c Complex.I z * p z + c z * b z)) = _
  rw [hthird1, hthird2, hmix]
  ring

end Yau.LeafProofs
