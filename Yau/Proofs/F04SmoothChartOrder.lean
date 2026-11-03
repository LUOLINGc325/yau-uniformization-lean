import Yau.Proofs.F04SupportedChartOrder
import Yau.LeafProofs.L16WeakLocalization

open MeasureTheory Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine smooth representative satisfies the original physical
 supported-pivot bounds at EVERY positive-time point, not just at almost
 every slice or for an arbitrary L2 representative. -/
theorem smooth_supported_energy_chart_bounds
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) {S : ℝ}
    (U : ℝ → DirichletEnergy g μ hμ Ω) (a : ℝ → Lp ℝ 2 (μ.restrict Ω))
    (r : M.Carrier → ℝ → ℝ) {u v : Point n → ℝ}
    (hu : MemLp u 2 (productVolume O (Ioo 0 S)))
    (hr : MemLp (fun q : Point n => r (chartInv c q.1) q.2) 2 (productVolume O (Ioo 0 S)))
    (hSlices : ∀ᵐ t ∂volume.restrict (Ioo 0 S),
      (fun z => u (z,t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (scalarEnergyL2 g μ hμ (U t).val))
    (haJ : ∀ᵐ t ∂volume.restrict (Ioo 0 S), a t = dirichletL2 g μ hμ Ω (U t))
    (ha : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ a t x ∧ a t x ≤ r x t)
    (hAE : u =ᵐ[productVolume O (Ioo 0 S)] v)
    (hv : ContinuousOn v (O ×ˢ Ioo 0 S))
    (hrC : ContinuousOn (fun q : Point n => r (chartInv c q.1) q.2) (O ×ˢ Ioo 0 S)) :
    ∀ q ∈ O ×ˢ Ioo 0 S, 0 ≤ v q ∧ v q ≤ r (chartInv c q.1) q.2 := by
  obtain ⟨hl,hh⟩ := supported_energy_chart_joint_bounds g μ hμ Ω hΩ c hO hOC hOt hMap U a r
    hu hr hSlices haJ ha
  have hLow : (fun _ : Point n => (0 : ℝ)) ≤ᵐ[productVolume O (Ioo 0 S)] v := by
    filter_upwards [hl,hAE] with q hq he
    rw [← he]
    exact hq
  have hUp : v ≤ᵐ[productVolume O (Ioo 0 S)] (fun q => r (chartInv c q.1) q.2) := by
    filter_upwards [hh,hAE] with q hq he
    rw [← he]
    exact hq
  rw [productVolume_eq_restrict] at hLow hUp
  have hQ : IsOpen (O ×ˢ Ioo (0 : ℝ) S) := hO.prod isOpen_Ioo
  intro q hq
  exact ⟨continuousOn_le_of_ae_le hQ continuousOn_const hv hLow q hq,
    continuousOn_le_of_ae_le hQ hv hrC hUp q hq⟩

end Yau.F04Proof
