import Yau.LeafProofs.L19HeatFamilyReal

/-! The positive-time inverse-resolvent factor and actual energy representative. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Division by the resolvent parameter has its continuous value zero at zero. -/
def scalarHeatInverseMultiplier (t s : ℝ) : ℝ := scalarHeatMultiplier t s / s

@[simp] theorem scalarHeatInverseMultiplier_zero (t : ℝ) : scalarHeatInverseMultiplier t 0 = 0 := by
  simp [scalarHeatInverseMultiplier]

theorem scalarHeatInverseMultiplier_eq_glue {t : ℝ} (ht : 0 < t) (s : ℝ) :
    scalarHeatInverseMultiplier t s = (Real.exp t / t) *
      ((s / t)⁻¹ * expNegInvGlue (s / t)) := by
  rw [scalarHeatInverseMultiplier, scalarHeatMultiplier_eq_glue ht]
  by_cases hs : s = 0
  · simp [hs]
  · field_simp

theorem scalarHeatInverseMultiplier_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (scalarHeatInverseMultiplier t) := by
  have hg : Continuous (fun x : ℝ => x⁻¹ * expNegInvGlue x) := by
    simpa only [Polynomial.eval_X] using
      expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  change Continuous (fun s => scalarHeatInverseMultiplier t s)
  simp_rw [scalarHeatInverseMultiplier_eq_glue ht]
  exact continuous_const.mul (hg.comp (continuous_id.div_const t))

theorem scalarHeatInverseMultiplier_mul (t s : ℝ) :
    s * scalarHeatInverseMultiplier t s = scalarHeatMultiplier t s := by
  by_cases hs : s = 0
  · simp [hs]
  · unfold scalarHeatInverseMultiplier
    field_simp

/-- The scalar time derivative is continuous in the spectral parameter at
all positive times. -/
theorem scalarHeatMultiplier_hasDerivAt (t s : ℝ) :
    HasDerivAt (fun u => scalarHeatMultiplier u s)
      (scalarHeatMultiplier t s - scalarHeatInverseMultiplier t s) t := by
  by_cases hs : 0 < s
  · have h := (((hasDerivAt_id t).neg).mul_const (s⁻¹ - 1)).exp
    simp only [Pi.neg_apply, id_eq] at h
    convert h using 1
    · ext u
      rw [scalarHeatMultiplier_of_pos u hs]
    · rw [scalarHeatInverseMultiplier, scalarHeatMultiplier_of_pos t hs]
      rw [div_eq_mul_inv]
      ring
  · have hz : ∀ u, scalarHeatMultiplier u s = 0 := by intro u; simp [scalarHeatMultiplier, hs]
    simpa only [hz, scalarHeatInverseMultiplier, zero_div, sub_zero] using (hasDerivAt_const t (0 : ℝ))

variable {n : ℕ} {M : ComplexManifold n}

/-- This is an actual bounded operator defined by the fixed continuous
functional calculus, with no chosen heat-family premise. -/
def scalarComplexHeatInverse (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  cfc (scalarHeatInverseMultiplier t) (scalarComplexResolvent g μ hμ)

theorem scalarComplexHeat_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    scalarComplexHeat g μ hμ t = scalarComplexResolvent g μ hμ * scalarComplexHeatInverse g μ hμ t := by
  rw [scalarComplexHeat_of_pos g μ hμ ht, scalarComplexHeatInverse]
  calc
    _ = cfc (fun s => s * scalarHeatInverseMultiplier t s) (scalarComplexResolvent g μ hμ) := by
      apply cfc_congr
      intro s _
      exact (scalarHeatInverseMultiplier_mul t s).symm
    _ = cfc (fun s : ℝ => s) (scalarComplexResolvent g μ hμ) *
        cfc (scalarHeatInverseMultiplier t) (scalarComplexResolvent g μ hμ) :=
      cfc_mul _ _ _ continuous_id.continuousOn (scalarHeatInverseMultiplier_continuous ht).continuousOn
    _ = _ := by rw [cfc_id' ℝ _ (scalarComplexResolvent_selfAdjoint g μ hμ)]

theorem scalarComplexHeatInverse_im_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) (v : Lp ℂ 2 μ)
    (hv : heatLpIm μ v = 0) : heatLpIm μ (scalarComplexHeatInverse g μ hμ t v) = 0 :=
  scalarComplexResolvent_cfc_im_zero g μ hμ _ (scalarHeatInverseMultiplier_continuous ht).continuousOn v hv

def scalarHeatInverse (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (heatLpRe μ).comp (((scalarComplexHeatInverse g μ hμ t).restrictScalars ℝ).comp (heatLpOfReal μ))

theorem scalarHeatInverse_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (f : Lp ℝ 2 μ) :
    scalarHeatInverse g μ hμ t f = heatLpRe μ (scalarComplexHeatInverse g μ hμ t (heatLpOfReal μ f)) := rfl

theorem scalarHeatInverse_ofReal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    heatLpOfReal μ (scalarHeatInverse g μ hμ t f) =
      scalarComplexHeatInverse g μ hμ t (heatLpOfReal μ f) := by
  have hd := heatLp_decomposition μ (scalarComplexHeatInverse g μ hμ t (heatLpOfReal μ f))
  rw [scalarComplexHeatInverse_im_zero g μ hμ ht _ (heatLpIm_ofReal μ f), map_zero,
    smul_zero, add_zero] at hd
  exact hd

theorem scalarHeatFamily_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    scalarHeatFamily g μ hμ t = scalarResolvent g μ hμ 1 zero_lt_one * scalarHeatInverse g μ hμ t := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Function.LeftInverse.injective (heatLpRe_ofReal μ))
  rw [mul_apply_eq_comp, scalarHeatFamily_ofReal, ← scalarComplexResolvent_ofReal,
    scalarHeatInverse_ofReal g μ hμ ht, scalarComplexHeat_factor g μ hμ ht, mul_apply_eq_comp]

/-- The actual energy representative of the positive-time heat flow. -/
def scalarHeatEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) : Lp ℝ 2 μ →L[ℝ] ScalarEnergySpace g μ hμ :=
  (scalarEnergyL2 g μ hμ).adjoint.comp (scalarHeatInverse g μ hμ t)

theorem scalarHeatEnergy_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    scalarEnergyL2 g μ hμ (scalarHeatEnergy g μ hμ t f) = scalarHeatFamily g μ hμ t f := by
  rw [scalarHeatFamily_factor g μ hμ ht, scalarResolvent_one_eq]
  rfl

theorem scalarHeatEnergy_weak (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ)
    (v : ScalarEnergySpace g μ hμ) :
    scalarClosedEnergy g μ hμ (scalarHeatEnergy g μ hμ t f) v =
      ⟪scalarHeatInverse g μ hμ t f - scalarHeatFamily g μ hμ t f,
        scalarEnergyL2 g μ hμ v⟫_ℝ := by
  rw [scalarClosedEnergy, scalarHeatEnergy_L2 g μ hμ ht, inner_sub_left]
  change ⟪(scalarEnergyL2 g μ hμ).adjoint (scalarHeatInverse g μ hμ t f), v⟫_ℝ - _ = _
  rw [ContinuousLinearMap.adjoint_inner_left]

end Yau.LeafProofs.L19Aux
