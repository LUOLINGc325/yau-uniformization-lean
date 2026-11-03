import Yau.Proofs.F03DirichletEulerResolvent
import Yau.Proofs.F03DirichletHeatDerivative
import Yau.LeafProofs.L19HeatMarkovEuler

/-! Operator-norm convergence of the actual supported Euler powers to the constructed heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- Actual dyadic implicit Euler powers at a positive time. -/
def dirichletHeatEuler (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    Lp ℝ 2 (μ.restrict O) →L[ℝ] Lp ℝ 2 (μ.restrict O) :=
  dirichletStepResolvent g μ hμ O (t / scalarEulerCount k)
    (div_pos ht (scalarEulerCount_cast_pos k)) ^ scalarEulerCount k

theorem dirichletHeatEuler_complexify (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    heatComplexify (μ.restrict O) (dirichletHeatEuler g μ hμ O t ht k) =
      cfc (scalarEulerPowerMultiplier t k) (dirichletComplexResolvent g μ hμ O) := by
  rw [dirichletHeatEuler, heatComplexify_pow, dirichletStepResolvent_complexify_eq_cfc,
    ← cfc_pow (scalarEulerMultiplier (t / scalarEulerCount k)) (scalarEulerCount k)
      (dirichletComplexResolvent g μ hμ O)
      ((scalarEulerMultiplier_continuousOn (div_pos ht (scalarEulerCount_cast_pos k))).mono
        (dirichletComplexResolvent_spectrum g μ hμ O))
      (dirichletComplexResolvent_selfAdjoint g μ hμ O)]
  rfl

/-- The CFC maps the uniform scalar Euler limit to convergence in operator
norm for the actual complexified variational operators. -/
theorem dirichletComplexHeat_euler_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k => heatComplexify (μ.restrict O) (dirichletHeatEuler g μ hμ O t ht k)) atTop
      (𝓝 (dirichletComplexHeat g μ hμ O t)) := by
  let B := dirichletComplexResolvent g μ hμ O
  let π : C(spectrum ℝ B, Set.Icc (0 : ℝ) 1) :=
    ⟨fun s => ⟨s, dirichletComplexResolvent_spectrum g μ hμ O s.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let A := (cfcL (R := ℝ) (dirichletComplexResolvent_selfAdjoint g μ hμ O)).comp
    (ContinuousMap.compCLM ℝ ℝ π)
  have heq (k : ℕ) : A
      (⟨fun s : Set.Icc (0 : ℝ) 1 => scalarEulerPowerMultiplier t k s,
        (scalarEulerPowerMultiplier_continuousOn ht k).domRestrict⟩ :
          C(Set.Icc (0 : ℝ) 1, ℝ)) =
        heatComplexify (μ.restrict O) (dirichletHeatEuler g μ hμ O t ht k) := by
    rw [dirichletHeatEuler_complexify, cfc_eq_cfcL
      (dirichletComplexResolvent_selfAdjoint g μ hμ O)
      ((scalarEulerPowerMultiplier_continuousOn ht k).mono
        (dirichletComplexResolvent_spectrum g μ hμ O))]
    rfl
  have hlim : A
      (⟨fun s : Set.Icc (0 : ℝ) 1 => scalarHeatMultiplier t s,
        (scalarHeatMultiplier_continuous ht).comp continuous_subtype_val⟩ :
          C(Set.Icc (0 : ℝ) 1, ℝ)) = dirichletComplexHeat g μ hμ O t := by
    rw [dirichletComplexHeat_of_pos g μ hμ O ht, cfc_eq_cfcL
      (dirichletComplexResolvent_selfAdjoint g μ hμ O)
      (scalarHeatMultiplier_continuous ht).continuousOn]
    rfl
  have h := A.continuous.continuousAt.tendsto.comp (scalarEulerPowerMultiplier_uniform ht)
  simpa only [Function.comp_def, heq, hlim] using h

/-- The genuine real heat family is the operator norm limit of its actual
variational implicit Euler powers. The time and geometry are the only
operator parameters; no Euler-limit premise is present. -/
theorem dirichletHeat_euler_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (ht : 0 < t) :
    Tendsto (dirichletHeatEuler g μ hμ O t ht) atTop (𝓝 (dirichletHeat g μ hμ O t)) := by
  have h := (heatRealRestrictionCLM (μ.restrict O)).continuous.continuousAt.tendsto.comp
    (dirichletComplexHeat_euler_tendsto g μ hμ O t ht)
  simpa only [Function.comp_def, heatRealRestrictionCLM_complexify,
    dirichletHeat_realRestriction] using h

/-- Explicit operator norm form of the Euler limit. -/
theorem dirichletHeat_euler_opNorm_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k => ‖dirichletHeatEuler g μ hμ O t ht k - dirichletHeat g μ hμ O t‖)
      atTop (𝓝 (0 : ℝ)) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (dirichletHeat_euler_tendsto g μ hμ O t ht)

/-- In particular Euler powers converge in actual L² on every input. -/
theorem dirichletHeat_euler_apply_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O)) :
    Tendsto (fun k => dirichletHeatEuler g μ hμ O t ht k f) atTop
      (𝓝 (dirichletHeat g μ hμ O t f)) := by
  exact (ContinuousLinearMap.apply ℝ (Lp ℝ 2 (μ.restrict O)) f).continuous.continuousAt.tendsto.comp
    (dirichletHeat_euler_tendsto g μ hμ O t ht)

end Yau.Proofs.F03Aux
