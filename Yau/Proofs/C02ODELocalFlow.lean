import Yau.LeafProofs.L12ODEVariation

/-! Actual local flows and their first variations, constructed from the native
Picard--Taylor--Gronwall theorem. The finite-order upgrade keeps this same ODE. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
universe u
namespace Yau.Blueprint.C02Proof

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure LocalVariationalFlow (F : E → E) (z₀ : E) (U : Set E) where
  radius : ℝ
  duration : ℝ
  radius_pos : 0 < radius
  duration_pos : 0 < duration
  solution : E → ℝ → E
  variation : E → ℝ → E →L[ℝ] E
  regularity : ContDiffOn ℝ 1 (Function.uncurry solution)
    (Metric.ball z₀ radius ×ˢ Ioo (-duration) duration)
  variation_continuous : ContinuousOn (Function.uncurry variation)
    (Metric.ball z₀ radius ×ˢ Ioo (-duration) duration)
  initial : ∀ z ∈ Metric.ball z₀ radius,
    solution z 0 = z ∧ variation z 0 = ContinuousLinearMap.id ℝ E
  equation : ∀ z ∈ Metric.ball z₀ radius, ∀ t ∈ Ioo (-duration) duration,
    solution z t ∈ U ∧ HasDerivAt (solution z) (F (solution z t)) t ∧
      HasDerivAt (variation z) ((fderiv ℝ F (solution z t)).comp (variation z t)) t
  space_derivative : ∀ p ∈ Metric.ball z₀ radius ×ˢ Ioo (-duration) duration,
    HasFDerivAt (fun z => solution z p.2) (variation p.1 p.2) p.1
  joint_derivative : ∀ p ∈ Metric.ball z₀ radius ×ˢ Ioo (-duration) duration,
    HasFDerivAt (Function.uncurry solution)
      ((variation p.1 p.2).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (F (solution p.1 p.2)))) p

namespace LocalVariationalFlow

variable {F : E → E} {z₀ : E} {U : Set E}

def domain (d : LocalVariationalFlow F z₀ U) : Set (E × ℝ) :=
  Metric.ball z₀ d.radius ×ˢ Ioo (-d.duration) d.duration

theorem domain_open (d : LocalVariationalFlow F z₀ U) : IsOpen d.domain :=
  Metric.isOpen_ball.prod isOpen_Ioo

theorem center_mem (d : LocalVariationalFlow F z₀ U) : (z₀, 0) ∈ d.domain :=
  ⟨Metric.mem_ball_self d.radius_pos, by constructor <;> linarith [d.duration_pos]⟩

theorem domain_mem_nhds (d : LocalVariationalFlow F z₀ U) : d.domain ∈ 𝓝 (z₀, 0) :=
  d.domain_open.mem_nhds d.center_mem

theorem solution_center (d : LocalVariationalFlow F z₀ U) : d.solution z₀ 0 = z₀ :=
  (d.initial z₀ (Metric.mem_ball_self d.radius_pos)).1

theorem variation_center (d : LocalVariationalFlow F z₀ U) :
    d.variation z₀ 0 = ContinuousLinearMap.id ℝ E :=
  (d.initial z₀ (Metric.mem_ball_self d.radius_pos)).2

theorem solution_continuousAt (d : LocalVariationalFlow F z₀ U) :
    ContinuousAt (Function.uncurry d.solution) (z₀, 0) :=
  d.regularity.continuousOn.continuousAt d.domain_mem_nhds

theorem variation_continuousAt (d : LocalVariationalFlow F z₀ U) :
    ContinuousAt (Function.uncurry d.variation) (z₀, 0) :=
  d.variation_continuous.continuousAt d.domain_mem_nhds

theorem pair_equation (d : LocalVariationalFlow F z₀ U)
    {z : E} (hz : z ∈ Metric.ball z₀ d.radius)
    {t : ℝ} (ht : t ∈ Ioo (-d.duration) d.duration) :
    HasDerivAt (fun s => (d.solution z s, d.variation z s))
      (Yau.LeafProofs.L12Aux.odeVariationField F (d.solution z t, d.variation z t)) t :=
  (d.equation z hz t ht).2.1.prodMk (d.equation z hz t ht).2.2

end LocalVariationalFlow

theorem exists_localVariationalFlow [CompleteSpace E]
    {F : E → E} {z₀ : E} {U : Set E}
    (hF : ContDiffAt ℝ 2 F z₀) (hU : IsOpen U) (hz₀ : z₀ ∈ U) :
    Nonempty (LocalVariationalFlow F z₀ U) := by
  obtain ⟨r, hr, ε, hε, φ, V, hφ, hV, hi, he, hs, hj⟩ :=
    Yau.LeafProofs.L12Aux.exists_C1_local_ODE_flow hF hU hz₀
  exact ⟨⟨r, ε, hr, hε, φ, V, hφ, hV, hi, he, hs, hj⟩⟩

theorem odeVariationField_smoothAt {F : E → E} {z₀ : E}
    (hF : ContDiffAt ℝ ∞ F z₀) :
    ContDiffAt ℝ ∞ (Yau.LeafProofs.L12Aux.odeVariationField F)
      (z₀, ContinuousLinearMap.id ℝ E) := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ F) z₀ := hF.fderiv_right (by simp)
  exact (hF.comp _ contDiffAt_fst).prodMk
    ((hD.comp _ contDiffAt_fst).clm_comp contDiffAt_snd)

end Yau.Blueprint.C02Proof
