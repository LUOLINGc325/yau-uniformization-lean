import Yau.Proofs.V03FourierEnergy
import Yau.Proofs.V03DirichletContinuity

/-! Uniform convergence of actual angular derivatives gives convergence in
the original homogeneous half-derivative seminorm. -/

open scoped Topology
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem uniform_derivative_sqIntegral_tendsto {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] (V : α → ℝ → ℂ) (v : ℝ → ℂ)
    (hV : ∀ᶠ a in l, Continuous (V a)) (hv : Continuous v)
    (hu : TendstoUniformlyOn V v l (Set.Icc 0 (2 * Real.pi))) :
    Tendsto (fun a => ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖V a θ - v θ‖ ^ 2) l (𝓝 0) := by
  have hbound := (Metric.tendstoUniformlyOn_iff.mp hu) 1 zero_lt_one
  have hnonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hmeas : ∀ᶠ a in l, AEStronglyMeasurable
      (fun θ => ‖V a θ - v θ‖ ^ 2) (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    filter_upwards [hV] with a ha
    exact ((ha.sub hv).norm.pow 2).aestronglyMeasurable
  have hdom : ∀ᶠ a in l, ∀ᵐ θ ∂volume, θ ∈ Set.uIoc 0 (2 * Real.pi) →
      ‖‖V a θ - v θ‖ ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [hbound] with a ha
    apply Eventually.of_forall
    intro θ hθ
    have hi : θ ∈ Set.Icc 0 (2 * Real.pi) := by
      simpa only [Set.uIcc_of_le hnonneg] using Set.uIoc_subset_uIcc hθ
    have hd := ha θ hi
    rw [dist_eq_norm, norm_sub_rev] at hd
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (V a θ - v θ)]
  have hlim : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc 0 (2 * Real.pi) →
      Tendsto (fun a => ‖V a θ - v θ‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro θ hθ
    have hi : θ ∈ Set.Icc 0 (2 * Real.pi) := by
      simpa only [Set.uIcc_of_le hnonneg] using Set.uIoc_subset_uIcc hθ
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hu.tendsto_at hi).sub_const (v θ)).norm.pow 2
  simpa only [intervalIntegral.integral_zero] using
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) hmeas hdom intervalIntegrable_const hlim

theorem boundaryDSq_sub_toReal_tendsto_of_uniform_derivative {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] (U V : α → ℝ → ℂ) (u v : ℝ → ℂ)
    (hU : ∀ᶠ a in l, (∀ θ, HasDerivAt (U a) (V a θ) θ) ∧ Continuous (V a) ∧
      U a (2 * Real.pi) = U a 0)
    (hu : ∀ θ, HasDerivAt u (v θ) θ) (hv : Continuous v)
    (hperiod : u (2 * Real.pi) = u 0)
    (hunif : TendstoUniformlyOn V v l (Set.Icc 0 (2 * Real.pi))) :
    Tendsto (fun a => (boundaryDSq (fun θ (_ : Unit) => U a θ - u θ)).toReal) l (𝓝 0) := by
  have hI := uniform_derivative_sqIntegral_tendsto V v (hU.mono fun a ha => ha.2.1) hv hunif
  have hR : Tendsto (fun a => (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖V a θ - v θ‖ ^ 2) l (𝓝 0) := by
    simpa only [mul_zero] using hI.const_mul (2 * Real.pi)⁻¹
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) ?_ hR
  filter_upwards [hU] with a ha
  have hdiff (θ : ℝ) : HasDerivAt (fun t => U a t - u t) (V a θ - v θ) θ :=
    (ha.1 θ).sub (hu θ)
  have hc := ha.2.1.sub hv
  have hb := boundaryDSq_le_angularDerivative (fun θ _ => hdiff θ)
    (hc.intervalIntegrable _ _) (by rw [ha.2.2, hperiod]) (continuous_memLp_circleInterval hc)
  have hnn : 0 ≤ (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖V a θ - v θ‖ ^ 2 :=
    mul_nonneg (by positivity) (intervalIntegral.integral_nonneg_of_forall
      (by positivity) (fun θ => sq_nonneg _))
  have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rwa [ENNReal.toReal_ofReal hnn] at hm

end Yau.Blueprint.V03Proof
