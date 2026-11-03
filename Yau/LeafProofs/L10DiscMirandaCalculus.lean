import Yau.LeafProofs.L10DiscEnergyCalculus
import Yau.LeafProofs.L10DiscBoundaryFrame

/-! Real within-disc partial derivatives for the Miranda--Talenti identity. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs

theorem discMiranda_partial_coordinates (u : ℂ → ℝ) (v z : ℂ) :
    discEnergyPartial u v z = v.re * discEnergyPartial u 1 z +
      v.im * discEnergyPartial u Complex.I z := by
  unfold discEnergyPartial
  conv_lhs => rw [discBoundary_real_coordinates v]
  rw [map_add, map_smul, map_smul]
  rfl

theorem discMiranda_partial_clm {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {u : ℂ → F} (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (L : F →L[ℝ] G) (v : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (L ∘ u) v z = L (discEnergyPartial u v z) := by
  have hd := L.hasFDerivAt.comp_hasFDerivWithinAt z
    (((hu.differentiableOn (by simp)) z hz).hasFDerivWithinAt)
  rw [discEnergyPartial, hd.fderivWithin (disc_closedBall_uniqueDiffOn z hz)]
  rfl

theorem discMiranda_partial_mul {a b : ℂ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Metric.closedBall (0 : ℂ) 1))
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1))
    (v : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (a * b) v z = discEnergyPartial a v z * b z + a z * discEnergyPartial b v z := by
  have h := ((((ha.differentiableOn (by simp)) z hz).hasFDerivWithinAt).mul
    (((hb.differentiableOn (by simp)) z hz).hasFDerivWithinAt)).fderivWithin
      (disc_closedBall_uniqueDiffOn z hz)
  have hh := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) h
  simpa [discEnergyPartial, mul_comm, add_comm] using hh

theorem discMiranda_partial_sub {a b : ℂ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Metric.closedBall (0 : ℂ) 1))
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1))
    (v : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (a - b) v z = discEnergyPartial a v z - discEnergyPartial b v z := by
  have h := ((((ha.differentiableOn (by simp)) z hz).hasFDerivWithinAt).sub
    (((hb.differentiableOn (by simp)) z hz).hasFDerivWithinAt)).fderivWithin
      (disc_closedBall_uniqueDiffOn z hz)
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L v) h

theorem discMiranda_partial_twice_eq {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (a b : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (discEnergyPartial u a) b z =
      fderivWithin ℝ (fderivWithin ℝ u (Metric.closedBall (0 : ℂ) 1))
        (Metric.closedBall (0 : ℂ) 1) z b a := by
  have hd : DifferentiableWithinAt ℝ (fderivWithin ℝ u (Metric.closedBall (0 : ℂ) 1))
      (Metric.closedBall (0 : ℂ) 1) z :=
    ((hu.fderivWithin (m := ∞) disc_closedBall_uniqueDiffOn (by simp)).differentiableOn (by simp)) z hz
  change (fderivWithin ℝ (fun y => fderivWithin ℝ u (Metric.closedBall (0 : ℂ) 1) y a)
      (Metric.closedBall (0 : ℂ) 1) z) b = _
  rw [fderivWithin_clm_apply (disc_closedBall_uniqueDiffOn z hz) hd (differentiableWithinAt_const a)]
  simp [ContinuousLinearMap.flip_apply]

theorem discMiranda_partial_commute {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (a b : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (discEnergyPartial u a) b z = discEnergyPartial (discEnergyPartial u b) a z := by
  have hc : z ∈ closure (interior (Metric.closedBall (0 : ℂ) 1)) := by
    rw [interior_closedBall 0 (by norm_num), closure_ball 0 (by norm_num)]
    exact hz
  have hs := (hu z hz).isSymmSndFDerivWithinAt (by simp) disc_closedBall_uniqueDiffOn hc hz
  rw [discMiranda_partial_twice_eq hu a b hz, discMiranda_partial_twice_eq hu b a hz]
  exact hs b a

theorem discMiranda_circle_derivative {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) (θ : ℝ) :
    HasDerivAt (fun t => u (L08_unitCircle t))
      (-(L08_unitCircle θ).im * discEnergyPartial u 1 (L08_unitCircle θ) +
        (L08_unitCircle θ).re * discEnergyPartial u Complex.I (L08_unitCircle θ)) θ := by
  have h := discEnergyPartial_hasDerivAt_circle hu θ
  rw [discMiranda_partial_coordinates] at h
  simpa using h

end Yau.LeafProofs
