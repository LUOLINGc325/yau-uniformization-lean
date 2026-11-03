import Yau.LeafProofs.L19HeatRegularityJoint
import Yau.LeafProofs.L19HeatRegularityTimeSlices
import Yau.LeafProofs.L16WeakLocalization

/-! Joint chart representatives and genuine local energy of the actual
constructed heat family on positive compact time slabs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual energy lift is a Bochner-L² path on every positive finite
slab. Its bound comes from continuity of the constructed lift. -/
theorem scalarHeatEnergy_memLp_slab (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) {l r : ℝ} (hl : 0 < l) :
    MemLp (fun t => scalarHeatEnergy g μ hμ t f) 2 (volume.restrict (Set.Ioo l r)) := by
  let W := fun t => scalarHeatEnergy g μ hμ t f
  have hc : ContinuousOn W (Set.Icc l r) := fun t ht =>
    (scalarHeatEnergy_continuousAt g μ hμ (hl.trans_le ht.1) f).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  apply MemLp.of_bound ((hc.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC ⟨t,Set.Ioo_subset_Icc_self ht,rfl⟩

/-- Genuine joint representatives of the constructed heat values and
completed chart derivatives, with actual L² slice identities. -/
theorem scalarHeat_chart_jointRepresentatives (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l) (f : Lp ℝ 2 μ) :
    ∃ (u : Parabolic.Point n → ℝ) (G : Parabolic.Point n → RIdx n → ℝ),
      StronglyMeasurable u ∧ (∀ i, StronglyMeasurable (fun p => G p i)) ∧
      MemLp u 2 (Parabolic.productVolume O (Set.Ioo l r)) ∧
      (∀ i, MemLp (fun p => G p i) 2 (Parabolic.productVolume O (Set.Ioo l r))) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        ((fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f)) ∧
        ∀ i, (fun z => G (z,t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i (scalarHeatEnergy g μ hμ t f) := by
  have hOvol : volume O < (⊤ : ENNReal) := lt_of_le_of_lt (measure_mono subset_closure) hOc.measure_lt_top
  have : IsFiniteMeasure (volume.restrict O) := isFiniteMeasure_restrict.mpr hOvol.ne
  let W := fun t => scalarHeatEnergy g μ hμ t f
  let R := (scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt).comp (scalarEnergyL2 g μ hμ)
  let D := fun i => scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
  have hW : MemLp W 2 (volume.restrict (Set.Ioo l r)) := scalarHeatEnergy_memLp_slab g μ hμ f hl
  obtain ⟨u,huM,huL,huSlice⟩ := scalarL2Path_exists_joint (R.comp_memLp' hW)
  have hgrad (i : RIdx n) := scalarL2Path_exists_joint ((D i).comp_memLp' hW)
  choose G hGM hGL hGS using hgrad
  refine ⟨u,(fun p i => G i p),huM,hGM,huL,hGL,?_⟩
  have hGSall := ae_all_iff.mpr hGS
  filter_upwards [huSlice,hGSall,ae_restrict_mem measurableSet_Ioo] with t ht hGt htI
  refine ⟨?_,hGt⟩
  have hJW := scalarHeatEnergy_L2 g μ hμ (hl.trans htI.1) f
  simpa only [Function.comp_apply, R, ContinuousLinearMap.comp_apply, W, hJW] using ht

/-- Every genuine spacetime test has genuine compact smooth spatial slices. -/
theorem scalarChartTest_slice {O : Set (Parabolic.Space n)} {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) (t : ℝ) :
    ContDiff ℝ ∞ (fun z => φ (z,t)) ∧ HasCompactSupport (fun z => φ (z,t)) ∧
      tsupport (fun z => φ (z,t)) ⊆ O := by
  have hsupport : tsupport (fun z => φ (z,t)) ⊆ (fun z => (z,t)) ⁻¹' tsupport φ :=
    tsupport_comp_subset_preimage φ (continuous_id.prodMk continuous_const)
  refine ⟨hφ.1.comp (contDiff_id.prodMk contDiff_const),?_,?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (hφ.2.1.image continuous_fst)
    intro z hz
    exact ⟨(z,t),hsupport (subset_tsupport _ hz),rfl⟩
  · intro z hz
    exact (hφ.2.2 (hsupport hz)).1

/-- Fubini turns the constructed slice identities and the genuine
completed spatial gradient theorem into the exact frozen spacetime weak
gradient identity. -/
theorem scalarHeat_chart_jointWeakGradient (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l) (f : Lp ℝ 2 μ)
    {u : Parabolic.Point n → ℝ} {G : Parabolic.Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hSlices : ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        ((fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f)) ∧
        ∀ i, (fun z => G (z,t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i (scalarHeatEnergy g μ hμ t f)) :
    Parabolic.WeakGradient O (Set.Ioo l r) u G := by
  intro φ hφ i
  have hφL : MemLp φ 2 (Parabolic.productVolume O (Set.Ioo l r)) := by
    rw [L16Aux.productVolume_eq_restrict]
    exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict _
  have hφD := L16Aux.test_spatialDerivative hφ i
  have hφDL : MemLp (fun p => Parabolic.d (fun z => φ (z,p.2)) p.1 i) 2
      (Parabolic.productVolume O (Set.Ioo l r)) := by
    rw [L16Aux.productVolume_eq_restrict]
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
  filter_upwards [hSlices,ae_restrict_mem measurableSet_Ioo] with t ht htI
  change (∫ z in O, u (z,t) * Parabolic.d (fun z => φ (z,t)) z i) =
    -(∫ z in O, G (z,t) i * φ (z,t))
  have hL : (∫ z in O, u (z,t) * Parabolic.d (fun z => φ (z,t)) z i) =
      ∫ z in O, scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
        (scalarHeatFamily g μ hμ t f) z * rDeriv (fun z => φ (z,t)) z i := by
    apply integral_congr_ae
    filter_upwards [ht.1] with z hz
    rw [hz]
    rfl
  have hR : (∫ z in O, G (z,t) i * φ (z,t)) =
      ∫ z in O, scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
        (scalarHeatEnergy g μ hμ t f) z * φ (z,t) := by
    apply integral_congr_ae
    filter_upwards [ht.2 i] with z hz
    rw [hz]
  rw [hL,hR]
  have hTest := scalarChartTest_slice hφ t
  exact scalarHeat_chartWeakGradient g μ hμ x hO hOc hOt (hl.trans htI.1) f
    (hTest.1.of_le (by simp)) hTest.2.1 hTest.2.2 i

/-- Genuine frozen LocalEnergy for actual heat chart representatives,
with all representatives, gradients, integrability and slice identities
constructed internally on every positive compact time slab. -/
theorem scalarHeat_chartLocalEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l) (f : Lp ℝ 2 μ) :
    ∃ (u : Parabolic.Point n → ℝ) (G : Parabolic.Point n → RIdx n → ℝ),
      StronglyMeasurable u ∧ (∀ i, StronglyMeasurable (fun p => G p i)) ∧
      Parabolic.LocalEnergy O (Set.Ioo l r) u G ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        ((fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f)) ∧
        ∀ i, (fun z => G (z,t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i (scalarHeatEnergy g μ hμ t f) := by
  obtain ⟨u,G,huM,hGM,hu,hG,hSlices⟩ := scalarHeat_chart_jointRepresentatives g μ hμ x hO hOc hOt hl f
  refine ⟨u,G,huM,hGM,⟨scalarHeat_chart_jointWeakGradient g μ hμ x hO hOc hOt hl f hu hG hSlices,?_⟩,
    hSlices⟩
  intro V c e _hV _hVC hVO hI
  have hm : Parabolic.productVolume V (Set.Ioo c e) ≤ Parabolic.productVolume O (Set.Ioo l r) :=
    Measure.prod_mono (Measure.restrict_mono (subset_closure.trans hVO) le_rfl)
      (Measure.restrict_mono (Set.Ioo_subset_Icc_self.trans hI) le_rfl)
  exact ⟨hu.mono_measure hm,fun i => (hG i).mono_measure hm⟩

end Yau.LeafProofs.L19Aux
