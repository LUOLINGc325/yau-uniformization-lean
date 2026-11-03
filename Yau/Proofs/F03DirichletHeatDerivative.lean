import Yau.Proofs.F03DirichletHeatEnergy
import Yau.LeafProofs.L19HeatFamilyDerivative

/-! Operator-norm time differentiation and the actual supported weak heat equation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

/-- Logarithmic time keeps the multiplier inside the positive-time region. -/
def dirichletHeatLogContinuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (a : ℝ) :
    C(spectrum ℝ (dirichletComplexResolvent g μ hμ O), ℝ) :=
  ⟨fun s => scalarHeatMultiplier (Real.exp a) s,
    (scalarHeatMultiplier_continuous (Real.exp_pos a)).comp continuous_subtype_val⟩

def dirichletHeatLogInverseContinuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (a : ℝ) :
    C(spectrum ℝ (dirichletComplexResolvent g μ hμ O), ℝ) :=
  ⟨fun s => scalarHeatInverseMultiplier (Real.exp a) s,
    (scalarHeatInverseMultiplier_continuous (Real.exp_pos a)).comp continuous_subtype_val⟩

def dirichletHeatLogDerivativeContinuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (a : ℝ) :
    C(spectrum ℝ (dirichletComplexResolvent g μ hμ O), ℝ) :=
  Real.exp a • (dirichletHeatLogContinuous g μ hμ O a - dirichletHeatLogInverseContinuous g μ hμ O a)

theorem dirichletHeatLogDerivative_continuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) : Continuous (dirichletHeatLogDerivativeContinuous g μ hμ O) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × spectrum ℝ (dirichletComplexResolvent g μ hμ O) =>
    Real.exp p.1 * (scalarHeatMultiplier (Real.exp p.1) p.2 - scalarHeatInverseMultiplier (Real.exp p.1) p.2))
  simp_rw [scalarHeatMultiplier_eq_glue (Real.exp_pos _),
    scalarHeatInverseMultiplier_eq_glue (Real.exp_pos _)]
  have hT : Continuous (fun p : ℝ × spectrum ℝ (dirichletComplexResolvent g μ hμ O) => Real.exp p.1) :=
    Real.continuous_exp.comp continuous_fst
  have hq : Continuous (fun p : ℝ × spectrum ℝ (dirichletComplexResolvent g μ hμ O) =>
      (p.2 : ℝ) / Real.exp p.1) :=
    (continuous_subtype_val.comp continuous_snd).div hT (fun _ => Real.exp_ne_zero _)
  have hg : Continuous (fun x : ℝ => x⁻¹ * expNegInvGlue x) := by
    simpa only [Polynomial.eval_X] using
      expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  exact hT.mul (((Real.continuous_exp.comp hT).mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp hq)).sub
    (((Real.continuous_exp.comp hT).div hT (fun _ => Real.exp_ne_zero _)).mul (hg.comp hq)))

theorem dirichletHeatLogContinuous_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (a : ℝ) :
    HasDerivAt (dirichletHeatLogContinuous g μ hμ O) (dirichletHeatLogDerivativeContinuous g μ hμ O a) a := by
  apply heatContinuousMap_hasDerivAt _ _ (dirichletHeatLogDerivative_continuous g μ hμ O)
  intro b s
  have h := (scalarHeatMultiplier_hasDerivAt (Real.exp b) (s : ℝ)).comp b (Real.hasDerivAt_exp b)
  simpa only [dirichletHeatLogContinuous, dirichletHeatLogDerivativeContinuous,
    dirichletHeatLogInverseContinuous, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, smul_eq_mul, mul_comm, Function.comp_def] using h

theorem dirichletHeatLog_cfcL (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (a : ℝ) :
    cfcL (dirichletComplexResolvent_selfAdjoint g μ hμ O) (dirichletHeatLogContinuous g μ hμ O a) =
      dirichletComplexHeat g μ hμ O (Real.exp a) := by
  rw [dirichletComplexHeat_of_pos g μ hμ O (Real.exp_pos a),
    cfc_eq_cfcL (dirichletComplexResolvent_selfAdjoint g μ hμ O)
      (scalarHeatMultiplier_continuous (Real.exp_pos a)).continuousOn]
  rfl

theorem dirichletHeatLogInverse_cfcL (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (a : ℝ) :
    cfcL (dirichletComplexResolvent_selfAdjoint g μ hμ O) (dirichletHeatLogInverseContinuous g μ hμ O a) =
      dirichletComplexHeatInverse g μ hμ O (Real.exp a) := by
  rw [dirichletComplexHeatInverse,
    cfc_eq_cfcL (dirichletComplexResolvent_selfAdjoint g μ hμ O)
      (scalarHeatInverseMultiplier_continuous (Real.exp_pos a)).continuousOn]
  rfl

theorem dirichletHeatLogDerivative_cfcL (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (a : ℝ) :
    cfcL (dirichletComplexResolvent_selfAdjoint g μ hμ O) (dirichletHeatLogDerivativeContinuous g μ hμ O a) =
      Real.exp a • (dirichletComplexHeat g μ hμ O (Real.exp a) - dirichletComplexHeatInverse g μ hμ O (Real.exp a)) := by
  rw [dirichletHeatLogDerivativeContinuous, map_smul, map_sub, dirichletHeatLog_cfcL, dirichletHeatLogInverse_cfcL]

theorem dirichletComplexHeat_log_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (a : ℝ) :
    HasDerivAt (fun b => dirichletComplexHeat g μ hμ O (Real.exp b))
      (Real.exp a • (dirichletComplexHeat g μ hμ O (Real.exp a) - dirichletComplexHeatInverse g μ hμ O (Real.exp a))) a := by
  have h := HasFDerivAt.comp_hasDerivAt
    (𝕜 := ℝ) (F := C(spectrum ℝ (dirichletComplexResolvent g μ hμ O), ℝ))
    (E := Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O))
    (f := dirichletHeatLogContinuous g μ hμ O) a
    (cfcL (R := ℝ) (dirichletComplexResolvent_selfAdjoint g μ hμ O)).hasFDerivAt
    (dirichletHeatLogContinuous_hasDerivAt g μ hμ O a)
  simpa only [Function.comp_def, dirichletHeatLog_cfcL, dirichletHeatLogDerivative_cfcL] using h

/-- The time derivative exists in operator norm at every positive time and
is the actual bounded energy factor dictated by the same CFC. -/
theorem dirichletComplexHeat_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (dirichletComplexHeat g μ hμ O)
      (dirichletComplexHeat g μ hμ O t - dirichletComplexHeatInverse g μ hμ O t) t := by
  have h := (dirichletComplexHeat_log_hasDerivAt g μ hμ O (Real.log t)).scomp t
    (Real.hasDerivAt_log ht.ne')
  rw [Real.exp_log ht] at h
  have h' : HasDerivAt (fun u => dirichletComplexHeat g μ hμ O (Real.exp (Real.log u)))
      (dirichletComplexHeat g μ hμ O t - dirichletComplexHeatInverse g μ hμ O t) t := by
    simpa only [Function.comp_def, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using h
  apply h'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with u hu
  rw [Real.exp_log hu]

@[simp] theorem dirichletHeat_realRestriction (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) :
    heatRealRestrictionCLM (μ.restrict O) (dirichletComplexHeat g μ hμ O t) = dirichletHeat g μ hμ O t := rfl

@[simp] theorem dirichletHeatInverse_realRestriction (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) :
    heatRealRestrictionCLM (μ.restrict O) (dirichletComplexHeatInverse g μ hμ O t) = dirichletHeatInverse g μ hμ O t := rfl

theorem dirichletHeat_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (dirichletHeat g μ hμ O)
      (dirichletHeat g μ hμ O t - dirichletHeatInverse g μ hμ O t) t := by
  have h := (heatRealRestrictionCLM (μ.restrict O)).hasFDerivAt.comp_hasDerivAt t
    (dirichletComplexHeat_hasDerivAt g μ hμ O ht)
  simpa only [Function.comp_def, map_sub, dirichletHeat_realRestriction, dirichletHeatInverse_realRestriction] using h

theorem dirichletHeat_apply_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O)) :
    HasDerivAt (fun u => dirichletHeat g μ hμ O u f)
      (dirichletHeat g μ hμ O t f - dirichletHeatInverse g μ hμ O t f) t := by
  have h := (ContinuousLinearMap.apply ℝ (Lp ℝ 2 (μ.restrict O)) f).hasFDerivAt.comp_hasDerivAt t
    (dirichletHeat_hasDerivAt g μ hμ O ht)
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, sub_apply] using h

/-- The actual energy completion solves the scalar heat equation in weak
form, with its time derivative proved in the original L² norm. -/
theorem dirichletHeat_weak_equation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O))
    (v : DirichletEnergy g μ hμ O) :
    ⟪deriv (fun u => dirichletHeat g μ hμ O u f) t, dirichletL2 g μ hμ O v⟫_ℝ +
      dirichletClosedEnergy g μ hμ O (dirichletHeatEnergy g μ hμ O t f) v = 0 := by
  rw [(dirichletHeat_apply_hasDerivAt g μ hμ O ht f).deriv, dirichletHeatEnergy_weak g μ hμ O ht,
    inner_sub_left, inner_sub_left]
  ring

theorem dirichletHeatLogInverse_continuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) : Continuous (dirichletHeatLogInverseContinuous g μ hμ O) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × spectrum ℝ (dirichletComplexResolvent g μ hμ O) =>
    scalarHeatInverseMultiplier (Real.exp p.1) p.2)
  simp_rw [scalarHeatInverseMultiplier_eq_glue (Real.exp_pos _)]
  have hT : Continuous (fun p : ℝ × spectrum ℝ (dirichletComplexResolvent g μ hμ O) => Real.exp p.1) :=
    Real.continuous_exp.comp continuous_fst
  have hq : Continuous (fun p : ℝ × spectrum ℝ (dirichletComplexResolvent g μ hμ O) =>
      (p.2 : ℝ) / Real.exp p.1) :=
    (continuous_subtype_val.comp continuous_snd).div hT (fun _ => Real.exp_ne_zero _)
  have hg : Continuous (fun x : ℝ => x⁻¹ * expNegInvGlue x) := by
    simpa only [Polynomial.eval_X] using
      expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  exact ((Real.continuous_exp.comp hT).div hT (fun _ => Real.exp_ne_zero _)).mul (hg.comp hq)

theorem dirichletComplexHeatInverse_log_continuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    Continuous (fun a => dirichletComplexHeatInverse g μ hμ O (Real.exp a)) := by
  have h := (cfcL (R := ℝ) (dirichletComplexResolvent_selfAdjoint g μ hμ O)).continuous.comp
    (dirichletHeatLogInverse_continuous g μ hμ O)
  simpa only [Function.comp_def, dirichletHeatLogInverse_cfcL] using h

theorem dirichletComplexHeatInverse_continuousAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (dirichletComplexHeatInverse g μ hμ O) t := by
  have h := (dirichletComplexHeatInverse_log_continuous g μ hμ O).continuousAt.comp
    (Real.continuousAt_log ht.ne')
  change ContinuousAt (fun u => dirichletComplexHeatInverse g μ hμ O (Real.exp (Real.log u))) t at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with u hu
  rw [Real.exp_log hu]

theorem dirichletHeatInverse_continuousAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (dirichletHeatInverse g μ hμ O) t := by
  have h := (heatRealRestrictionCLM (μ.restrict O)).continuous.continuousAt.comp
    (dirichletComplexHeatInverse_continuousAt g μ hμ O ht)
  simpa only [Function.comp_def, dirichletHeatInverse_realRestriction] using h

/-- The actual energy representative varies continuously in its genuine H¹
completion on every positive-time interval. -/
theorem dirichletHeatEnergy_continuousAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O)) :
    ContinuousAt (fun u => dirichletHeatEnergy g μ hμ O u f) t := by
  have h := (dirichletL2 g μ hμ O).adjoint.continuous.continuousAt.comp
    ((ContinuousLinearMap.apply ℝ (Lp ℝ 2 (μ.restrict O)) f).continuous.continuousAt.comp
      (dirichletHeatInverse_continuousAt g μ hμ O ht))
  exact h

end Yau.Proofs.F03Aux
