import Yau.LeafProofs.L19KernelRegularizedCore
import Yau.LeafProofs.L19WeightedTrace

/-! The original kernel acts on regularized compact tests by the actual heat. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- Fixed-slab duality and the original compact trace identify the
regularized test action, before any total kernel mass has been proved. -/
theorem scalarHeatKernel_regularized_core_identity (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ} (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    (k : ScalarEnergyDomain g μ hμ) (y : M.Carrier) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    Integrable (fun x => H T x y * scalarClassicalHeat hn g hK μ hμ
      (scalarEnergyDomainL2 g μ hμ k) x ε) μ ∧
    (∫ x, H T x y * scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) x ε ∂μ) =
      scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) y (T + ε) := by
  let v := scalarCoreBackwardTest hn g hK μ hμ k T ε
  let Q := ∫ x, H T x y * scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) x ε ∂μ
  have hi := (scalarHeatKernel_regularized_core_duality hn g hcomplete hK hRic μ hμ hH k y hT hε hT le_rfl).2.1
  refine ⟨hi, ?_⟩
  obtain ⟨C, β, hC, hβ, htail⟩ := scalarCoreBackwardTest_gaussian_tail hn g hcomplete hK hRic μ hμ k y hT hε
  have hslab : Icc (0 : ℝ) T ⊆ Iio (T + ε) := by
    intro s hs
    change s < T + ε
    exact lt_of_le_of_lt hs.2 (lt_add_of_pos_right T hε)
  have htrace := scalarHeatKernel_moving_gaussian_trace hn g hcomplete hK hRic μ hμ hH y y
    isOpen_Iio (scalarCoreBackwardTest_smooth hn g hK μ hμ k T ε) hT hslab hC hβ htail
  have heq : (fun s : ℝ => ∫ x, H s x y * v x s ∂μ) =ᶠ[𝓝[>] 0] fun _ => Q := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with s hs hsT
    exact (scalarHeatKernel_regularized_core_duality hn g hcomplete hK hRic μ hμ hH k y hT hε hs hsT.le).2.2
  have hconst : Tendsto (fun s : ℝ => ∫ x, H s x y * v x s ∂μ) (𝓝[>] 0) (𝓝 Q) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => Q) (𝓝[>] 0) (𝓝 Q)).congr' heq.symm
  have hQ := tendsto_nhds_unique hconst htrace
  simpa only [v, scalarCoreBackwardTest, sub_zero] using hQ

end Yau.LeafProofs.L19Aux
