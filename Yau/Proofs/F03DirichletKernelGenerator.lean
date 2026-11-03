import Yau.Proofs.F03DirichletKernelEvolution
import Yau.Proofs.F03DirichletGeneratorIntegral
import Yau.Proofs.F03DirichletHeatInitial

/-! The literal initial L² and two-way generator clauses for the one actual kernel. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The actual kernel source integral has the registered initial L² limit. -/
theorem dirichletKernelCandidate_initial_scalarL2DistanceSq (g : SmoothMetric M)
    (hK : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : M.Carrier → ℝ)
    (hf : ScalarL2 (μ.restrict Ω) f) :
    Tendsto (fun t : ℝ => scalarL2DistanceSq (μ.restrict Ω)
      (boundedKernelEvolution μ (dirichletKernelCandidate g hK μ hμ Ω hΩ) f t) f)
      (𝓝[>] 0) (𝓝 0) := by
  have hl := dirichletHeat_initial_scalarL2DistanceSq g μ hμ Ω hΩ f hf
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  unfold scalarL2DistanceSq
  apply lintegral_congr_ae
  filter_upwards [dirichletKernelCandidate_evolution_ae g hK μ hμ Ω hΩ (show 0 < t from ht) f hf] with x hx
  rw [hx]

/-- Both directions of the original prequotient Friedrichs generator
criterion hold for the SAME constructed kernel's actual integral evolution. -/
theorem dirichletKernelCandidate_generator_iff (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f w : M.Carrier → ℝ)
    (hf : ScalarL2 (μ.restrict Ω) f) (hw : ScalarL2 (μ.restrict Ω) w) :
    ScalarFriedrichsPair g.form μ Ω f w ↔
      Tendsto (fun t : ℝ => ∫⁻ x in Ω, ENNReal.ofReal
        (|((boundedKernelEvolution μ (dirichletKernelCandidate g hK μ hμ Ω hΩ) f t x - f x) / t) + w x| ^ 2) ∂μ)
        (𝓝[>] 0) (𝓝 0) := by
  rw [scalarFriedrichsPair_iff_heat_generator_integral g μ hμ Ω hΩ f w hf hw]
  have heq : (fun t : ℝ => ∫⁻ x in Ω, ENNReal.ofReal
      (|((dirichletHeat g μ hμ Ω t (scalarToLp hf) x - f x) / t) + w x| ^ 2) ∂μ) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => ∫⁻ x in Ω, ENNReal.ofReal
        (|((boundedKernelEvolution μ (dirichletKernelCandidate g hK μ hμ Ω hΩ) f t x - f x) / t) + w x| ^ 2) ∂μ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply lintegral_congr_ae
    filter_upwards [dirichletKernelCandidate_evolution_ae g hK μ hμ Ω hΩ (show 0 < t from ht) f hf] with x hx
    rw [hx]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

end Yau.Proofs.F03Aux
