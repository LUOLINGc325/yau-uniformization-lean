import Yau.LeafProofs.L19HeatMarkovResolvent

/-! Operator norm convergence of the actual dyadic Euler powers. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Actual dyadic implicit Euler powers at a positive time. -/
def scalarHeatEuler (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  scalarResolvent g μ hμ (t / scalarEulerCount k)
    (div_pos ht (scalarEulerCount_cast_pos k)) ^ scalarEulerCount k

theorem scalarHeatEuler_complexify (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    heatComplexify μ (scalarHeatEuler g μ hμ t ht k) =
      cfc (scalarEulerPowerMultiplier t k) (scalarComplexResolvent g μ hμ) := by
  rw [scalarHeatEuler, heatComplexify_pow, scalarResolvent_complexify_eq_cfc,
    ← cfc_pow (scalarEulerMultiplier (t / scalarEulerCount k)) (scalarEulerCount k)
      (scalarComplexResolvent g μ hμ)
      ((scalarEulerMultiplier_continuousOn (div_pos ht (scalarEulerCount_cast_pos k))).mono
        (scalarComplexResolvent_spectrum g μ hμ))
      (scalarComplexResolvent_selfAdjoint g μ hμ)]
  rfl

/-- The CFC maps the uniform scalar Euler limit to convergence in operator
norm for the actual complexified variational operators. -/
theorem scalarComplexHeat_euler_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k => heatComplexify μ (scalarHeatEuler g μ hμ t ht k)) atTop
      (𝓝 (scalarComplexHeat g μ hμ t)) := by
  let B := scalarComplexResolvent g μ hμ
  let π : C(spectrum ℝ B, Set.Icc (0 : ℝ) 1) :=
    ⟨fun s => ⟨s, scalarComplexResolvent_spectrum g μ hμ s.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let A := (cfcL (R := ℝ) (scalarComplexResolvent_selfAdjoint g μ hμ)).comp
    (ContinuousMap.compCLM ℝ ℝ π)
  have heq (k : ℕ) : A
      (⟨fun s : Set.Icc (0 : ℝ) 1 => scalarEulerPowerMultiplier t k s,
        (scalarEulerPowerMultiplier_continuousOn ht k).domRestrict⟩ :
          C(Set.Icc (0 : ℝ) 1, ℝ)) =
        heatComplexify μ (scalarHeatEuler g μ hμ t ht k) := by
    rw [scalarHeatEuler_complexify, cfc_eq_cfcL
      (scalarComplexResolvent_selfAdjoint g μ hμ)
      ((scalarEulerPowerMultiplier_continuousOn ht k).mono
        (scalarComplexResolvent_spectrum g μ hμ))]
    rfl
  have hlim : A
      (⟨fun s : Set.Icc (0 : ℝ) 1 => scalarHeatMultiplier t s,
        (scalarHeatMultiplier_continuous ht).comp continuous_subtype_val⟩ :
          C(Set.Icc (0 : ℝ) 1, ℝ)) = scalarComplexHeat g μ hμ t := by
    rw [scalarComplexHeat_of_pos g μ hμ ht, cfc_eq_cfcL
      (scalarComplexResolvent_selfAdjoint g μ hμ)
      (scalarHeatMultiplier_continuous ht).continuousOn]
    rfl
  have h := A.continuous.continuousAt.tendsto.comp (scalarEulerPowerMultiplier_uniform ht)
  simpa only [Function.comp_def, heq, hlim] using h

/-- The genuine real heat family is the operator norm limit of its actual
variational implicit Euler powers. The time and geometry are the only
operator parameters; no Euler-limit premise is present. -/
theorem scalarHeatFamily_euler_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 < t) :
    Tendsto (scalarHeatEuler g μ hμ t ht) atTop (𝓝 (scalarHeatFamily g μ hμ t)) := by
  have h := (heatRealRestrictionCLM μ).continuous.continuousAt.tendsto.comp
    (scalarComplexHeat_euler_tendsto g μ hμ t ht)
  simpa only [Function.comp_def, heatRealRestrictionCLM_complexify,
    heatRealRestrictionCLM_heat] using h

/-- Explicit operator norm form of the Euler limit. -/
theorem scalarHeatFamily_euler_opNorm_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k => ‖scalarHeatEuler g μ hμ t ht k - scalarHeatFamily g μ hμ t‖)
      atTop (𝓝 (0 : ℝ)) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (scalarHeatFamily_euler_tendsto g μ hμ t ht)

/-- In particular Euler powers converge in actual L² on every input. -/
theorem scalarHeatFamily_euler_apply_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    Tendsto (fun k => scalarHeatEuler g μ hμ t ht k f) atTop
      (𝓝 (scalarHeatFamily g μ hμ t f)) := by
  exact (ContinuousLinearMap.apply ℝ (Lp ℝ 2 μ) f).continuous.continuousAt.tendsto.comp
    (scalarHeatFamily_euler_tendsto g μ hμ t ht)

end Yau.LeafProofs.L19Aux
