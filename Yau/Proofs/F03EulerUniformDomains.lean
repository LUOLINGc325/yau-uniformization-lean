import Yau.Proofs.F03HeatRestrictionBound

/-! A geometry-independent scalar Euler error bounds every actual domain operator. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def scalarEulerUniformError (t : ℝ) (ht : 0 < t) (k : ℕ) : ℝ :=
  ‖(⟨fun s : Icc (0 : ℝ) 1 => scalarEulerPowerMultiplier t k s,
      (scalarEulerPowerMultiplier_continuousOn ht k).domRestrict⟩ : C(Icc (0 : ℝ) 1,ℝ))-
    (⟨fun s : Icc (0 : ℝ) 1 => scalarHeatMultiplier t s,
      (scalarHeatMultiplier_continuous ht).comp continuous_subtype_val⟩ : C(Icc (0 : ℝ) 1,ℝ))‖

theorem scalarEulerUniformError_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (scalarEulerUniformError t ht) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (scalarEulerPowerMultiplier_uniform ht)

theorem dirichletComplexHeat_euler_uniform_bound (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    ‖heatComplexify (μ.restrict Ω) (dirichletHeatEuler g μ hμ Ω t ht k)-
      dirichletComplexHeat g μ hμ Ω t‖ ≤ scalarEulerUniformError t ht k := by
  rw [dirichletHeatEuler_complexify,dirichletComplexHeat_of_pos g μ hμ Ω ht,
    ← cfc_sub (scalarEulerPowerMultiplier t k) (scalarHeatMultiplier t)
      (dirichletComplexResolvent g μ hμ Ω)
      ((scalarEulerPowerMultiplier_continuousOn ht k).mono (dirichletComplexResolvent_spectrum g μ hμ Ω))
      (scalarHeatMultiplier_continuous ht).continuousOn]
  apply norm_cfc_le (norm_nonneg _)
  intro s hs
  exact ContinuousMap.norm_coe_le_norm
    ((⟨fun r : Icc (0 : ℝ) 1 => scalarEulerPowerMultiplier t k r,
        (scalarEulerPowerMultiplier_continuousOn ht k).domRestrict⟩ : C(Icc (0 : ℝ) 1,ℝ))-
      (⟨fun r : Icc (0 : ℝ) 1 => scalarHeatMultiplier t r,
        (scalarHeatMultiplier_continuous ht).comp continuous_subtype_val⟩ : C(Icc (0 : ℝ) 1,ℝ)))
    ⟨s,dirichletComplexResolvent_spectrum g μ hμ Ω hs⟩

theorem dirichletHeat_euler_uniform_bound (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    ‖dirichletHeatEuler g μ hμ Ω t ht k-dirichletHeat g μ hμ Ω t‖ ≤
      scalarEulerUniformError t ht k := by
  have hreal := heatRealRestrictionCLM_norm_le (μ.restrict Ω)
    (heatComplexify (μ.restrict Ω) (dirichletHeatEuler g μ hμ Ω t ht k)-dirichletComplexHeat g μ hμ Ω t)
  simp only [map_sub,heatRealRestrictionCLM_complexify,dirichletHeat_realRestriction] at hreal
  exact hreal.trans (dirichletComplexHeat_euler_uniform_bound g μ hμ Ω t ht k)

theorem dirichletHeat_euler_uniform_domains (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (ht : 0 < t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Ω : Set M.Carrier,
      ‖dirichletHeatEuler g μ hμ Ω t ht k-dirichletHeat g μ hμ Ω t‖ < ε := by
  obtain ⟨k₀,hk₀⟩ := eventually_atTop.mp ((scalarEulerUniformError_tendsto t ht).eventually
    (eventually_lt_nhds hε))
  exact ⟨k₀,fun k hk Ω => (dirichletHeat_euler_uniform_bound g μ hμ Ω t ht k).trans_lt (hk₀ k hk)⟩

end Yau.Proofs.F03Aux
