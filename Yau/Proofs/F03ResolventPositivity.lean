import Yau.Proofs.F03DirichletHeatPositivity
import Yau.Proofs.F03L2Order

/-! Positivity of the actual variational resolvents on all L2 inputs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem l2_positive_of_bounded_clips {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ K : ℝ, 0 < K → ∀ f : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K) → ∀ᵐ x ∂μ, 0 ≤ T f x)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) : ∀ᵐ x ∂μ, 0 ≤ T f x := by
  have hlim := T.continuous.continuousAt.tendsto.comp (normalClipL2_tendsto_of_nonneg μ f hf)
  have hbound (k : ℕ) : 0 ≤ T (normalClipL2 μ ((k : ℝ)+1) (by positivity) f) := by
    apply (Lp.coeFn_nonneg _).mp
    apply hT ((k : ℝ)+1) (by positivity)
    filter_upwards [normalClipL2_coe μ ((k : ℝ)+1) (by positivity) f] with x hx
    rw [hx]
    exact normalClip_mem_interval (by positivity) _
  apply (Lp.coeFn_nonneg _).mpr
  exact (isClosed_Ici : IsClosed {v : Lp ℝ 2 μ | 0 ≤ v}).mem_of_tendsto hlim
    (Eventually.of_forall hbound)

theorem scalarResolvent_nonneg (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) {h : ℝ} (hh : 0 < h)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∀ᵐ x ∂μ, 0 ≤ scalarResolvent g μ hμ h hh f x := by
  apply l2_positive_of_bounded_clips μ (scalarResolvent g μ hμ h hh) _ f hf
  intro K hK v hv
  exact (scalarResolvent_markov g μ hμ h hh K hK v hv).mono (fun _ h => h.1)

theorem dirichletStepResolvent_nonneg (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {h : ℝ} (hh : 0 < h)
    (f : Lp ℝ 2 (μ.restrict Ω)) (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x) :
    ∀ᵐ x ∂μ.restrict Ω, 0 ≤ dirichletStepResolvent g μ hμ Ω h hh f x := by
  apply l2_positive_of_bounded_clips (μ.restrict Ω) (dirichletStepResolvent g μ hμ Ω h hh) _ f hf
  intro K hK v hv
  exact (dirichletStepResolvent_markov g μ hμ Ω hΩ h hh K hK v hv).mono (fun _ h => h.1)

theorem scalarResolvent_monotone (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) {h : ℝ} (hh : 0 < h) :
    Monotone (scalarResolvent g μ hμ h hh) := by
  apply l2_linear_monotone μ μ
  intro f hf
  exact (Lp.coeFn_nonneg _).mp (scalarResolvent_nonneg g μ hμ hh f ((Lp.coeFn_nonneg _).mpr hf))

theorem dirichletStepResolvent_monotone (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {h : ℝ} (hh : 0 < h) :
    Monotone (dirichletStepResolvent g μ hμ Ω h hh) := by
  apply l2_linear_monotone (μ.restrict Ω) (μ.restrict Ω)
  intro f hf
  exact (Lp.coeFn_nonneg _).mp
    (dirichletStepResolvent_nonneg g μ hμ Ω hΩ hh f ((Lp.coeFn_nonneg _).mpr hf))

end Yau.Proofs.F03Aux
