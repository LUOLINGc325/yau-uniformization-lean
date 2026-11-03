import Yau.Proofs.F03DirichletAmbientEnergy
import Yau.LeafProofs.L19HeatRegularityLocalEnergy

/-! Genuine chart values and local energy for the supported heat family. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual zero-extended heat vector has the native completed chart
weak derivative, with the original g and μ in every map. -/
theorem dirichletHeat_chartWeakGradient (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (x : M.Carrier) {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOt : closure O ⊆ chartTarget x)
    {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict Ω))
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ 1 η)
    (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O) (i : RIdx n) :
    (∫ z in O, scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
        (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f)) z * rDeriv η z i) =
      -(∫ z in O, scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
        (dirichletAmbientHeatEnergy g μ hμ Ω t f) z * η z) := by
  rw [← dirichletAmbientHeatEnergy_L2 g μ hμ Ω hΩ ht f]
  exact scalarEnergy_chartWeakGradient g μ hμ x hO hOc hOt
    (dirichletAmbientHeatEnergy g μ hμ Ω t f) hη hcη hηO i

/-- All chart values and gradients admit actual jointly measurable L²
representatives, constructed from the same supported energy path. -/
theorem dirichletHeat_chart_jointRepresentatives (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l)
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    ∃ (u : Parabolic.Point n → ℝ) (G : Parabolic.Point n → RIdx n → ℝ),
      StronglyMeasurable u ∧ (∀ i, StronglyMeasurable (fun p => G p i)) ∧
      MemLp u 2 (Parabolic.productVolume O (Set.Ioo l r)) ∧
      (∀ i, MemLp (fun p => G p i) 2 (Parabolic.productVolume O (Set.Ioo l r))) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        ((fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
            (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))) ∧
        ∀ i, (fun z => G (z,t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
            (dirichletAmbientHeatEnergy g μ hμ Ω t f) := by
  have hOvol : volume O < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono subset_closure) hOc.measure_lt_top
  have : IsFiniteMeasure (volume.restrict O) := isFiniteMeasure_restrict.mpr hOvol.ne
  let W := fun t => dirichletAmbientHeatEnergy g μ hμ Ω t f
  let R := (scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt).comp (scalarEnergyL2 g μ hμ)
  let D := fun i => scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
  have hW : MemLp W 2 (volume.restrict (Set.Ioo l r)) :=
    dirichletAmbientHeatEnergy_memLp_slab g μ hμ Ω f hl
  obtain ⟨u,huM,huL,huSlice⟩ := scalarL2Path_exists_joint (R.comp_memLp' hW)
  have hgrad (i : RIdx n) := scalarL2Path_exists_joint ((D i).comp_memLp' hW)
  choose G hGM hGL hGS using hgrad
  refine ⟨u,(fun p i => G i p),huM,hGM,huL,hGL,?_⟩
  have hGSall := ae_all_iff.mpr hGS
  filter_upwards [huSlice,hGSall,ae_restrict_mem measurableSet_Ioo] with t ht hGt htI
  refine ⟨?_,hGt⟩
  have hJW := dirichletAmbientHeatEnergy_L2 g μ hμ Ω hΩ (hl.trans htI.1) f
  simpa only [Function.comp_apply,R,ContinuousLinearMap.comp_apply,W,hJW] using ht

/-- Fubini transports the already proved native weak derivatives of the
actual energy path to the frozen spacetime weak-gradient statement. -/
theorem dirichletHeat_chart_jointWeakGradient (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l)
    (f : Lp ℝ 2 (μ.restrict Ω))
    {u : Parabolic.Point n → ℝ} {G : Parabolic.Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hSlices : ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        ((fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
            (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))) ∧
        ∀ i, (fun z => G (z,t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
            (dirichletAmbientHeatEnergy g μ hμ Ω t f)) :
    Parabolic.WeakGradient O (Set.Ioo l r) u G := by
  intro φ hφ i
  have hφL : MemLp φ 2 (Parabolic.productVolume O (Set.Ioo l r)) := by
    rw [LeafProofs.L16Aux.productVolume_eq_restrict]
    exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict _
  have hφD := LeafProofs.L16Aux.test_spatialDerivative hφ i
  have hφDL : MemLp (fun p => Parabolic.d (fun z => φ (z,p.2)) p.1 i) 2
      (Parabolic.productVolume O (Set.Ioo l r)) := by
    rw [LeafProofs.L16Aux.productVolume_eq_restrict]
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
  rw [integral_prod_symm _ hiL,integral_prod_symm _ hiR,← integral_neg]
  apply integral_congr_ae
  filter_upwards [hSlices,ae_restrict_mem measurableSet_Ioo] with t ht htI
  change (∫ z in O, u (z,t) * Parabolic.d (fun z => φ (z,t)) z i) =
    -(∫ z in O, G (z,t) i * φ (z,t))
  have hL : (∫ z in O, u (z,t) * Parabolic.d (fun z => φ (z,t)) z i) =
      ∫ z in O, scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
        (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f)) z * rDeriv (fun z => φ (z,t)) z i := by
    apply integral_congr_ae
    filter_upwards [ht.1] with z hz
    rw [hz]
    rfl
  have hR : (∫ z in O, G (z,t) i * φ (z,t)) =
      ∫ z in O, scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
        (dirichletAmbientHeatEnergy g μ hμ Ω t f) z * φ (z,t) := by
    apply integral_congr_ae
    filter_upwards [ht.2 i] with z hz
    rw [hz]
  rw [hL,hR]
  have hTest := scalarChartTest_slice hφ t
  exact dirichletHeat_chartWeakGradient g μ hμ Ω hΩ x hO hOc hOt (hl.trans htI.1) f
    (hTest.1.of_le (by simp)) hTest.2.1 hTest.2.2 i

end Yau.Proofs.F03Aux
