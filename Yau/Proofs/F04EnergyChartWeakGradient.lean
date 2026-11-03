import Yau.Proofs.F04EnergyChartJoint
import Yau.LeafProofs.L19HeatRegularityLocalEnergy

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual joint representatives of a supported energy path have the
 genuine weak spatial differential. The identity follows from completed
 spatial integration by parts and actual Fubini, with no derivative data
 added to the energy path. -/
theorem dirichletEnergy_chart_jointWeakGradient (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier)
    (U : ℝ → DirichletEnergy g μ hμ Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ}
    {u : Parabolic.Point n → ℝ} {G : Parabolic.Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hSlices : ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        ((fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarEnergyL2 g μ hμ (U t).val)) ∧
        ∀ i, (fun z => G (z,t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i (U t).val) :
    Parabolic.WeakGradient O (Set.Ioo l r) u G := by
  intro φ hφ i
  have hφL : MemLp φ 2 (Parabolic.productVolume O (Set.Ioo l r)) := by
    rw [Yau.LeafProofs.L16Aux.productVolume_eq_restrict]
    exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict _
  have hφD := Yau.LeafProofs.L16Aux.test_spatialDerivative hφ i
  have hφDL : MemLp (fun p => Parabolic.d (fun z => φ (z,p.2)) p.1 i) 2
      (Parabolic.productVolume O (Set.Ioo l r)) := by
    rw [Yau.LeafProofs.L16Aux.productVolume_eq_restrict]
    exact (hφD.1.continuous.memLp_of_hasCompactSupport hφD.2.1).restrict _
  have hiL := hu.integrable_mul hφDL
  have hiR := (hG i).integrable_mul hφL
  change Integrable (fun p => u p * Parabolic.d (fun z => φ (z,p.2)) p.1 i)
    ((volume.restrict O).prod (volume.restrict (Set.Ioo l r))) at hiL
  change Integrable (fun p => G p i * φ p)
    ((volume.restrict O).prod (volume.restrict (Set.Ioo l r))) at hiR
  change (∫ p, u p * Parabolic.d (fun z => φ (z,p.2)) p.1 i
      ∂(volume.restrict O).prod (volume.restrict (Set.Ioo l r))) =
    -(∫ p, G p i * φ p ∂(volume.restrict O).prod (volume.restrict (Set.Ioo l r)))
  rw [integral_prod_symm _ hiL, integral_prod_symm _ hiR, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hSlices] with t ht
  change (∫ z in O, u (z,t) * Parabolic.d (fun z => φ (z,t)) z i) =
    -(∫ z in O, G (z,t) i * φ (z,t))
  have hL : (∫ z in O, u (z,t) * Parabolic.d (fun z => φ (z,t)) z i) =
      ∫ z in O, scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
        (scalarEnergyL2 g μ hμ (U t).val) z * rDeriv (fun z => φ (z,t)) z i := by
    apply integral_congr_ae
    filter_upwards [ht.1] with z hz
    rw [hz]
    rfl
  have hR : (∫ z in O, G (z,t) i * φ (z,t)) =
      ∫ z in O, scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
        (U t).val z * φ (z,t) := by
    apply integral_congr_ae
    filter_upwards [ht.2 i] with z hz
    rw [hz]
  rw [hL,hR]
  have hTest := scalarChartTest_slice hφ t
  exact scalarEnergy_chartWeakGradient g μ hμ x hO hOc hOt (U t).val
    (hTest.1.of_le (by simp)) hTest.2.1 hTest.2.2 i

/-- Product representatives constructed from an actual time-L2 energy
 path satisfy the literal local-energy predicate, including its weak
 gradient and every smaller-cylinder L2 requirement. -/
theorem dirichletEnergy_chart_localEnergy
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) {T : ℝ} (U : ℝ → DirichletEnergy g μ hμ Ω)
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T))) (c : M.Carrier)
    {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) :
    ∃ (u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ),
      StronglyMeasurable u ∧ (∀ i, StronglyMeasurable (fun p => G p i)) ∧
      LocalEnergy O (Ioo 0 T) u G ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T),
        ((fun z => u (z, t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (scalarEnergyL2 g μ hμ (U t).val)) ∧
        ∀ i, (fun z => G (z, t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt i (U t).val := by
  obtain ⟨u, G, huM, hGM, hu, hG, hSlices⟩ :=
    dirichletEnergy_chart_joint_representatives g μ hμ Ω U hU c hO hOC hOt
  refine ⟨u, G, huM, hGM, ⟨?_, ?_⟩, hSlices⟩
  · exact dirichletEnergy_chart_jointWeakGradient g μ hμ Ω U c hO hOC hOt hu hG hSlices
  · intro V a b _hV _hVC hVO hI
    have hm : productVolume V (Ioo a b) ≤ productVolume O (Ioo 0 T) :=
      Measure.prod_mono (Measure.restrict_mono (subset_closure.trans hVO) le_rfl)
        (Measure.restrict_mono (Ioo_subset_Icc_self.trans hI) le_rfl)
    exact ⟨hu.mono_measure hm, fun i => (hG i).mono_measure hm⟩

end Yau.F04Proof
