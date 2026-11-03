import Yau.LeafProofs.L19HeatFamilyPositiveTime
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Operator norm differentiability at positive times. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Pointwise derivatives with a continuous derivative in the compact sup norm
are derivatives in that norm. This follows from the Banach-valued fundamental
theorem of calculus and continuous point evaluations. -/
theorem heatContinuousMap_hasDerivAt {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (F D : ℝ → C(K, ℝ)) (hD : Continuous D)
    (hFD : ∀ t x, HasDerivAt (fun u => F u x) (D t x) t) (t : ℝ) :
    HasDerivAt F (D t) t := by
  have hi (u : ℝ) : (∫ a in t..u, D a) = F u - F t := by
    apply ContinuousMap.ext
    intro x
    have hcomm := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm (hD.intervalIntegrable (μ := volume) t u)
    change (∫ a in t..u, D a x) = (∫ a in t..u, D a) x at hcomm
    rw [← hcomm]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hFD a x)
      (((ContinuousMap.evalCLM ℝ x).continuous.comp hD).intervalIntegrable t u)
  have hI := intervalIntegral.integral_hasDerivAt_right (hD.intervalIntegrable (μ := volume) t t)
    hD.aestronglyMeasurable.stronglyMeasurableAtFilter (hD.continuousAt (x := t))
  simp_rw [hi] at hI
  simpa only [sub_add_cancel] using hI.add_const (F t)

variable {n : ℕ} {M : ComplexManifold n}

/-- Logarithmic time keeps the multiplier inside the positive-time region. -/
def scalarHeatLogContinuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : ℝ) :
    C(spectrum ℝ (scalarComplexResolvent g μ hμ), ℝ) :=
  ⟨fun s => scalarHeatMultiplier (Real.exp a) s,
    (scalarHeatMultiplier_continuous (Real.exp_pos a)).comp continuous_subtype_val⟩

def scalarHeatLogInverseContinuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : ℝ) :
    C(spectrum ℝ (scalarComplexResolvent g μ hμ), ℝ) :=
  ⟨fun s => scalarHeatInverseMultiplier (Real.exp a) s,
    (scalarHeatInverseMultiplier_continuous (Real.exp_pos a)).comp continuous_subtype_val⟩

def scalarHeatLogDerivativeContinuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : ℝ) :
    C(spectrum ℝ (scalarComplexResolvent g μ hμ), ℝ) :=
  Real.exp a • (scalarHeatLogContinuous g μ hμ a - scalarHeatLogInverseContinuous g μ hμ a)

theorem scalarHeatLogDerivative_continuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Continuous (scalarHeatLogDerivativeContinuous g μ hμ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × spectrum ℝ (scalarComplexResolvent g μ hμ) =>
    Real.exp p.1 * (scalarHeatMultiplier (Real.exp p.1) p.2 - scalarHeatInverseMultiplier (Real.exp p.1) p.2))
  simp_rw [scalarHeatMultiplier_eq_glue (Real.exp_pos _),
    scalarHeatInverseMultiplier_eq_glue (Real.exp_pos _)]
  have hT : Continuous (fun p : ℝ × spectrum ℝ (scalarComplexResolvent g μ hμ) => Real.exp p.1) :=
    Real.continuous_exp.comp continuous_fst
  have hq : Continuous (fun p : ℝ × spectrum ℝ (scalarComplexResolvent g μ hμ) =>
      (p.2 : ℝ) / Real.exp p.1) :=
    (continuous_subtype_val.comp continuous_snd).div hT (fun _ => Real.exp_ne_zero _)
  have hg : Continuous (fun x : ℝ => x⁻¹ * expNegInvGlue x) := by
    simpa only [Polynomial.eval_X] using
      expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  exact hT.mul (((Real.continuous_exp.comp hT).mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp hq)).sub
    (((Real.continuous_exp.comp hT).div hT (fun _ => Real.exp_ne_zero _)).mul (hg.comp hq)))

theorem scalarHeatLogContinuous_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : ℝ) :
    HasDerivAt (scalarHeatLogContinuous g μ hμ) (scalarHeatLogDerivativeContinuous g μ hμ a) a := by
  apply heatContinuousMap_hasDerivAt _ _ (scalarHeatLogDerivative_continuous g μ hμ)
  intro b s
  have h := (scalarHeatMultiplier_hasDerivAt (Real.exp b) (s : ℝ)).comp b (Real.hasDerivAt_exp b)
  simpa only [scalarHeatLogContinuous, scalarHeatLogDerivativeContinuous,
    scalarHeatLogInverseContinuous, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, smul_eq_mul, mul_comm, Function.comp_def] using h

theorem scalarHeatLog_cfcL (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : ℝ) :
    cfcL (scalarComplexResolvent_selfAdjoint g μ hμ) (scalarHeatLogContinuous g μ hμ a) =
      scalarComplexHeat g μ hμ (Real.exp a) := by
  rw [scalarComplexHeat_of_pos g μ hμ (Real.exp_pos a),
    cfc_eq_cfcL (scalarComplexResolvent_selfAdjoint g μ hμ)
      (scalarHeatMultiplier_continuous (Real.exp_pos a)).continuousOn]
  rfl

theorem scalarHeatLogInverse_cfcL (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : ℝ) :
    cfcL (scalarComplexResolvent_selfAdjoint g μ hμ) (scalarHeatLogInverseContinuous g μ hμ a) =
      scalarComplexHeatInverse g μ hμ (Real.exp a) := by
  rw [scalarComplexHeatInverse,
    cfc_eq_cfcL (scalarComplexResolvent_selfAdjoint g μ hμ)
      (scalarHeatInverseMultiplier_continuous (Real.exp_pos a)).continuousOn]
  rfl

theorem scalarHeatLogDerivative_cfcL (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : ℝ) :
    cfcL (scalarComplexResolvent_selfAdjoint g μ hμ) (scalarHeatLogDerivativeContinuous g μ hμ a) =
      Real.exp a • (scalarComplexHeat g μ hμ (Real.exp a) - scalarComplexHeatInverse g μ hμ (Real.exp a)) := by
  rw [scalarHeatLogDerivativeContinuous, map_smul, map_sub, scalarHeatLog_cfcL, scalarHeatLogInverse_cfcL]

theorem scalarComplexHeat_log_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : ℝ) :
    HasDerivAt (fun b => scalarComplexHeat g μ hμ (Real.exp b))
      (Real.exp a • (scalarComplexHeat g μ hμ (Real.exp a) - scalarComplexHeatInverse g μ hμ (Real.exp a))) a := by
  have h := HasFDerivAt.comp_hasDerivAt
    (𝕜 := ℝ) (F := C(spectrum ℝ (scalarComplexResolvent g μ hμ), ℝ))
    (E := Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (f := scalarHeatLogContinuous g μ hμ) a
    (cfcL (R := ℝ) (scalarComplexResolvent_selfAdjoint g μ hμ)).hasFDerivAt
    (scalarHeatLogContinuous_hasDerivAt g μ hμ a)
  simpa only [Function.comp_def, scalarHeatLog_cfcL, scalarHeatLogDerivative_cfcL] using h

/-- The time derivative exists in operator norm at every positive time and
is the actual bounded energy factor dictated by the same CFC. -/
theorem scalarComplexHeat_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarComplexHeat g μ hμ)
      (scalarComplexHeat g μ hμ t - scalarComplexHeatInverse g μ hμ t) t := by
  have h := (scalarComplexHeat_log_hasDerivAt g μ hμ (Real.log t)).scomp t
    (Real.hasDerivAt_log ht.ne')
  rw [Real.exp_log ht] at h
  have h' : HasDerivAt (fun u => scalarComplexHeat g μ hμ (Real.exp (Real.log u)))
      (scalarComplexHeat g μ hμ t - scalarComplexHeatInverse g μ hμ t) t := by
    simpa only [Function.comp_def, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using h
  apply h'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with u hu
  rw [Real.exp_log hu]

/-- Restriction to the actual real scalar L² space, as a bounded map on
operator spaces. It is used only after the real subspace invariance proof. -/
def heatRealRestrictionCLM {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) →L[ℝ] (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :=
  (ContinuousLinearMap.compL ℝ (Lp ℝ 2 μ) (Lp ℂ 2 μ) (Lp ℝ 2 μ) (heatLpRe μ)).comp
    (((ContinuousLinearMap.compL ℝ (Lp ℝ 2 μ) (Lp ℂ 2 μ) (Lp ℂ 2 μ)).flip (heatLpOfReal μ)).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ) ℝ ℝ))

@[simp] theorem heatRealRestrictionCLM_heat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) :
    heatRealRestrictionCLM μ (scalarComplexHeat g μ hμ t) = scalarHeatFamily g μ hμ t := rfl

@[simp] theorem heatRealRestrictionCLM_inverse (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) :
    heatRealRestrictionCLM μ (scalarComplexHeatInverse g μ hμ t) = scalarHeatInverse g μ hμ t := rfl

theorem scalarHeatFamily_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarHeatFamily g μ hμ)
      (scalarHeatFamily g μ hμ t - scalarHeatInverse g μ hμ t) t := by
  have h := (heatRealRestrictionCLM μ).hasFDerivAt.comp_hasDerivAt t
    (scalarComplexHeat_hasDerivAt g μ hμ ht)
  simpa only [Function.comp_def, map_sub, heatRealRestrictionCLM_heat, heatRealRestrictionCLM_inverse] using h

theorem scalarHeatFamily_apply_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    HasDerivAt (fun u => scalarHeatFamily g μ hμ u f)
      (scalarHeatFamily g μ hμ t f - scalarHeatInverse g μ hμ t f) t := by
  have h := (ContinuousLinearMap.apply ℝ (Lp ℝ 2 μ) f).hasFDerivAt.comp_hasDerivAt t
    (scalarHeatFamily_hasDerivAt g μ hμ ht)
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, sub_apply] using h

/-- The actual energy completion solves the scalar heat equation in weak
form, with its time derivative proved in the original L² norm. -/
theorem scalarHeatFamily_weak_equation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ)
    (v : ScalarEnergySpace g μ hμ) :
    ⟪deriv (fun u => scalarHeatFamily g μ hμ u f) t, scalarEnergyL2 g μ hμ v⟫_ℝ +
      scalarClosedEnergy g μ hμ (scalarHeatEnergy g μ hμ t f) v = 0 := by
  rw [(scalarHeatFamily_apply_hasDerivAt g μ hμ ht f).deriv, scalarHeatEnergy_weak g μ hμ ht,
    inner_sub_left, inner_sub_left]
  ring

theorem scalarHeatLogInverse_continuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Continuous (scalarHeatLogInverseContinuous g μ hμ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × spectrum ℝ (scalarComplexResolvent g μ hμ) =>
    scalarHeatInverseMultiplier (Real.exp p.1) p.2)
  simp_rw [scalarHeatInverseMultiplier_eq_glue (Real.exp_pos _)]
  have hT : Continuous (fun p : ℝ × spectrum ℝ (scalarComplexResolvent g μ hμ) => Real.exp p.1) :=
    Real.continuous_exp.comp continuous_fst
  have hq : Continuous (fun p : ℝ × spectrum ℝ (scalarComplexResolvent g μ hμ) =>
      (p.2 : ℝ) / Real.exp p.1) :=
    (continuous_subtype_val.comp continuous_snd).div hT (fun _ => Real.exp_ne_zero _)
  have hg : Continuous (fun x : ℝ => x⁻¹ * expNegInvGlue x) := by
    simpa only [Polynomial.eval_X] using
      expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  exact ((Real.continuous_exp.comp hT).div hT (fun _ => Real.exp_ne_zero _)).mul (hg.comp hq)

theorem scalarComplexHeatInverse_log_continuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    Continuous (fun a => scalarComplexHeatInverse g μ hμ (Real.exp a)) := by
  have h := (cfcL (R := ℝ) (scalarComplexResolvent_selfAdjoint g μ hμ)).continuous.comp
    (scalarHeatLogInverse_continuous g μ hμ)
  simpa only [Function.comp_def, scalarHeatLogInverse_cfcL] using h

theorem scalarComplexHeatInverse_continuousAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (scalarComplexHeatInverse g μ hμ) t := by
  have h := (scalarComplexHeatInverse_log_continuous g μ hμ).continuousAt.comp
    (Real.continuousAt_log ht.ne')
  change ContinuousAt (fun u => scalarComplexHeatInverse g μ hμ (Real.exp (Real.log u))) t at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with u hu
  rw [Real.exp_log hu]

theorem scalarHeatInverse_continuousAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (scalarHeatInverse g μ hμ) t := by
  have h := (heatRealRestrictionCLM μ).continuous.continuousAt.comp
    (scalarComplexHeatInverse_continuousAt g μ hμ ht)
  simpa only [Function.comp_def, heatRealRestrictionCLM_inverse] using h

/-- The actual energy representative varies continuously in its genuine H¹
completion on every positive-time interval. -/
theorem scalarHeatEnergy_continuousAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    ContinuousAt (fun u => scalarHeatEnergy g μ hμ u f) t := by
  have h := (scalarEnergyL2 g μ hμ).adjoint.continuous.continuousAt.comp
    ((ContinuousLinearMap.apply ℝ (Lp ℝ 2 μ) f).continuous.continuousAt.comp
      (scalarHeatInverse_continuousAt g μ hμ ht))
  exact h

end Yau.LeafProofs.L19Aux
