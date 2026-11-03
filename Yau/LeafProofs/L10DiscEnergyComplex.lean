import Yau.LeafProofs.L10DiscEnergyIdentities

/-! Real and imaginary energies recover the actual complex-valued energies. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.LeafProofs

def discEnergyGradientSq (u : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖discEnergyPartial u 1 z‖^2 + ‖discEnergyPartial u Complex.I z‖^2

def discEnergyHessianSq (u : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖discEnergyPartial (discEnergyPartial u 1) 1 z‖^2 +
  ‖discEnergyPartial (discEnergyPartial u 1) Complex.I z‖^2 +
  ‖discEnergyPartial (discEnergyPartial u Complex.I) 1 z‖^2 +
  ‖discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z‖^2

def discEnergyLaplacian (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  discEnergyPartial (discEnergyPartial u 1) 1 z +
    discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z

theorem discEnergyPartial_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {u : ℂ → E}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (v : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (fun w => L (u w)) v z = L (discEnergyPartial u v z) := by
  have h := L.hasFDerivAt.comp_hasFDerivWithinAt z
    (((hu.differentiableOn (by simp)) z hz).hasFDerivWithinAt)
  have heq := h.fderivWithin (disc_closedBall_uniqueDiffOn z hz)
  change fderivWithin ℝ (fun w => L (u w)) (Metric.closedBall (0 : ℂ) 1) z = _ at heq
  simpa only [discEnergyPartial, ContinuousLinearMap.comp_apply] using
    congrArg (fun D : ℂ →L[ℝ] F => D v) heq

theorem discEnergyPartial_twice_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {u : ℂ → E}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (v w : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyPartial (discEnergyPartial (fun y => L (u y)) v) w z =
      L (discEnergyPartial (discEnergyPartial u v) w z) := by
  have heq : EqOn (discEnergyPartial (fun y => L (u y)) v)
      (fun y => L (discEnergyPartial u v y)) (Metric.closedBall (0 : ℂ) 1) :=
    fun y hy => discEnergyPartial_clm L hu v hy
  change fderivWithin ℝ (discEnergyPartial (fun y => L (u y)) v)
    (Metric.closedBall (0 : ℂ) 1) z w = _
  rw [fderivWithin_congr heq (heq hz)]
  exact discEnergyPartial_clm L (discEnergyPartial_contDiffOn hu v) w hz

theorem discEnergy_norm_sq_re_im (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem discEnergyGradientSq_re_im {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyGradientSq u z =
      discEnergyRealGradientSq (fun w => (u w).re) z +
      discEnergyRealGradientSq (fun w => (u w).im) z := by
  have hr (v : ℂ) := discEnergyPartial_clm Complex.reCLM hu v hz
  have hi (v : ℂ) := discEnergyPartial_clm Complex.imCLM hu v hz
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hr hi
  simp only [discEnergyGradientSq, discEnergyRealGradientSq, hr, hi,
    discEnergy_norm_sq_re_im]
  ring

theorem discEnergyLaplacian_re_im {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyRealLaplacian (fun w => (u w).re) z = (discEnergyLaplacian u z).re ∧
    discEnergyRealLaplacian (fun w => (u w).im) z = (discEnergyLaplacian u z).im := by
  have hr (v w : ℂ) := discEnergyPartial_twice_clm Complex.reCLM hu v w hz
  have hi (v w : ℂ) := discEnergyPartial_twice_clm Complex.imCLM hu v w hz
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hr hi
  simp only [discEnergyLaplacian, discEnergyRealLaplacian, Complex.add_re,
    Complex.add_im, hr, hi, and_self]

theorem discEnergyLaplacian_eq_planar {u : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discEnergyLaplacian u z = LeafCandidates.planarLaplacian u z := by
  simp only [discEnergyLaplacian, discEnergyPartial_twice_eq u _ _ hz,
    LeafCandidates.planarLaplacian]

theorem discEnergyGradientSq_continuousOn {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discEnergyGradientSq u) (Metric.closedBall (0 : ℂ) 1) :=
  ((discEnergyPartial_contDiffOn hu 1).continuousOn.norm.pow 2).add
    ((discEnergyPartial_contDiffOn hu Complex.I).continuousOn.norm.pow 2)

theorem discEnergyLaplacian_continuousOn {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discEnergyLaplacian u) (Metric.closedBall (0 : ℂ) 1) :=
  ((discEnergyPartial_contDiffOn (discEnergyPartial_contDiffOn hu 1) 1).continuousOn).add
    ((discEnergyPartial_contDiffOn (discEnergyPartial_contDiffOn hu Complex.I) Complex.I).continuousOn)

theorem discEnergy_complex_first_order {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) :
    (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖^2) ≤
        ∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2 ∧
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) ≤
        ∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2 := by
  have hur : ContDiffOn ℝ ∞ (fun w => (u w).re) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ (fun w => (u w).im) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.imCLM.contDiff.comp_contDiffOn hu
  have hr := discEnergy_real_first_order hur (fun z hz => by rw [hzero z hz]; rfl)
  have hi := discEnergy_real_first_order hui (fun z hz => by rw [hzero z hz]; rfl)
  have hL : (∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2) =
      (∫ z in Metric.ball (0 : ℂ) 1, (discEnergyRealLaplacian (fun w => (u w).re) z)^2) +
      (∫ z in Metric.ball (0 : ℂ) 1, (discEnergyRealLaplacian (fun w => (u w).im) z)^2) := by
    have hFr : IntegrableOn (fun z => (discEnergyRealLaplacian (fun w => (u w).re) z)^2)
        (Metric.ball (0 : ℂ) 1) :=
      discEnergy_integrableOn ((discEnergyRealLaplacian_continuousOn hur).pow 2)
    have hFi : IntegrableOn (fun z => (discEnergyRealLaplacian (fun w => (u w).im) z)^2)
        (Metric.ball (0 : ℂ) 1) :=
      discEnergy_integrableOn ((discEnergyRealLaplacian_continuousOn hui).pow 2)
    rw [← integral_add hFr hFi]
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z hz
    dsimp only
    rw [(discEnergyLaplacian_re_im hu (Metric.ball_subset_closedBall hz)).1,
      (discEnergyLaplacian_re_im hu (Metric.ball_subset_closedBall hz)).2,
      discEnergy_norm_sq_re_im]
  have hU : (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖^2) =
      (∫ z in Metric.ball (0 : ℂ) 1, (u z).re^2) +
      (∫ z in Metric.ball (0 : ℂ) 1, (u z).im^2) := by
    simp_rw [discEnergy_norm_sq_re_im]
    exact integral_add (discEnergy_integrableOn (hur.continuousOn.pow 2))
      (discEnergy_integrableOn (hui.continuousOn.pow 2))
  have hG : (∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) =
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq (fun w => (u w).re) z) +
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq (fun w => (u w).im) z) := by
    rw [← integral_add (discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hur))
      (discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hui))]
    exact setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      (fun z hz => discEnergyGradientSq_re_im hu (Metric.ball_subset_closedBall hz))
  rw [hU, hG, hL]
  exact ⟨add_le_add hr.1 hi.1, add_le_add hr.2 hi.2⟩

end Yau.LeafProofs
