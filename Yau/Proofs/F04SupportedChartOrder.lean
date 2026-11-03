import Yau.Proofs.F04ChartOrderTransport
import Yau.Proofs.F04SupportedL2Pairing
import Yau.Proofs.F03DirichletEnergy

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual chart of a supported L2 class preserves its physical
 almost-everywhere lower and upper bounds. All zero-extension and chart
 representatives are identified in their actual measures. -/
theorem supportedL2_chart_ae_bounds
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω)
    (a : Lp ℝ 2 (μ.restrict Ω)) (r : M.Carrier → ℝ)
    (ha : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ a x ∧ a x ≤ r x) :
    ∀ᵐ z ∂volume.restrict O,
      0 ≤ scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ a) z ∧
      scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ a) z ≤ r (chartInv c z) := by
  have hZA : (l2ZeroExtension μ Ω hΩ a : M.Carrier → ℝ) =ᵐ[μ] Ω.indicator (a : M.Carrier → ℝ) :=
    extendL2_coe μ Ω hΩ a
  have hA := scalarEnergy_chart_ae_eq g μ hμ c hO hOC hOt hZA
  have hR := scalarEnergy_chartRestrictionCLM_coe g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ a)
  have hLow := chart_ae_le_of_supported_ae_le g μ hμ Ω hΩ c hO hOC hOt hMap
    (ha.mono (fun _ hx => hx.1))
  have hUp := chart_ae_le_of_supported_ae_le g μ hμ Ω hΩ c hO hOC hOt hMap
    (ha.mono (fun _ hx => hx.2))
  filter_upwards [hA,hR,hLow,hUp,ae_restrict_mem hO.measurableSet] with z hAz hRz hl hu hz
  rw [hRz,hAz,indicator_of_mem (hMap ⟨z,hz,rfl⟩)]
  exact ⟨hl,hu⟩

/-- The actual supported-energy joint representative inherits physical
 slice order in product measure. The original supported pivot trace and
 J(U) need agree only at the supplied almost-everywhere times. -/
theorem supported_energy_chart_joint_bounds
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) {S : ℝ}
    (U : ℝ → DirichletEnergy g μ hμ Ω) (a : ℝ → Lp ℝ 2 (μ.restrict Ω))
    (r : M.Carrier → ℝ → ℝ) {u : Yau.Parabolic.Point n → ℝ}
    (hu : MemLp u 2 (Yau.Parabolic.productVolume O (Ioo 0 S)))
    (hr : MemLp (fun q : Yau.Parabolic.Point n => r (chartInv c q.1) q.2) 2
      (Yau.Parabolic.productVolume O (Ioo 0 S)))
    (hSlices : ∀ᵐ t ∂volume.restrict (Ioo 0 S),
      (fun z => u (z,t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (scalarEnergyL2 g μ hμ (U t).val))
    (haJ : ∀ᵐ t ∂volume.restrict (Ioo 0 S), a t = dirichletL2 g μ hμ Ω (U t))
    (ha : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ a t x ∧ a t x ≤ r x t) :
    (∀ᵐ q ∂Yau.Parabolic.productVolume O (Ioo 0 S), 0 ≤ u q) ∧
      (∀ᵐ q ∂Yau.Parabolic.productVolume O (Ioo 0 S), u q ≤ r (chartInv c q.1) q.2) := by
  have hBound : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ z ∂volume.restrict O,
      0 ≤ u (z,t) ∧ u (z,t) ≤ r (chartInv c z) t := by
    filter_upwards [hSlices,haJ,ha] with t ht hJ hat
    have hB := supportedL2_chart_ae_bounds g μ hμ Ω hΩ c hO hOC hOt hMap (a t) (fun x => r x t) hat
    have hZ : l2ZeroExtension μ Ω hΩ (a t) = scalarEnergyL2 g μ hμ (U t).val := by
      rw [hJ,dirichletL2_zeroExtension]
    rw [hZ] at hB
    filter_upwards [ht,hB] with z hz hb
    rw [hz]
    exact hb
  constructor
  · exact product_memLp_ae_le_of_ae_time_slices (MemLp.zero) hu
      (hBound.mono (fun _ ht => ht.mono (fun _ hx => hx.1)))
  · exact product_memLp_ae_le_of_ae_time_slices hu hr
      (hBound.mono (fun _ ht => ht.mono (fun _ hx => hx.2)))

end Yau.F04Proof
