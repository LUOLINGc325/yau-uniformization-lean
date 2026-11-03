import Yau.Proofs.D02HolomorphicNormalFamily

/-! The same compact L¹ limit equals the actual potential of the metric
normal limit almost everywhere. This uses Fatou and pointwise convergence,
and does not replace the original limit by a newly chosen function. -/

open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem ae_eq_of_L1_and_pointwise {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (v : ℕ → α → ℝ) (u w : α → ℝ) (hv : ∀ j, Integrable (v j) ν)
    (hu : Integrable u ν) (hw : Integrable w ν)
    (hL1 : Tendsto (fun j => ∫ z, |v j z - u z| ∂ν) atTop (𝓝 0))
    (hpt : ∀ᵐ z ∂ν, Tendsto (fun j => v j z) atTop (𝓝 (w z))) : w =ᵐ[ν] u := by
  let e : ℕ → α → ℝ≥0∞ := fun j z => ENNReal.ofReal |v j z - u z|
  have hi (j : ℕ) : Integrable (fun z => |v j z - u z|) ν := (hv j |>.sub hu).abs
  have he (j : ℕ) : AEMeasurable (e j) ν := ENNReal.continuous_ofReal.measurable.comp_aemeasurable
    (hi j).aemeasurable
  have heq (j : ℕ) : (∫⁻ z, e j z ∂ν) = ENNReal.ofReal (∫ z, |v j z - u z| ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal (hi j) (Eventually.of_forall fun z => abs_nonneg _)).symm
  have hzero : Tendsto (fun j => ∫⁻ z, e j z ∂ν) atTop (𝓝 0) := by
    simpa only [heq, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL1
  have hlim : ∀ᵐ z ∂ν, Tendsto (fun j => e j z) atTop (𝓝 (ENNReal.ofReal |w z - u z|)) := by
    filter_upwards [hpt] with z hz
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hz.sub tendsto_const_nhds).abs
  have hIntZero : (∫⁻ z, ENNReal.ofReal |w z - u z| ∂ν) = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      _ = ∫⁻ z, liminf (fun j => e j z) atTop ∂ν :=
        lintegral_congr_ae (hlim.mono fun z hz => hz.liminf_eq.symm)
      _ ≤ liminf (fun j => ∫⁻ z, e j z ∂ν) atTop := lintegral_liminf_le' he
      _ = 0 := hzero.liminf_eq
  have hae := (lintegral_eq_zero_iff' (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
    (hw.sub hu).abs.aemeasurable)).mp hIntZero
  filter_upwards [hae] with z hz
  have habs : |w z - u z| = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

theorem immersionPotential_limit_ae_on_compact {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {O S : Set ℂ} (hO : IsOpen O) (hOD : O ⊆ ball (0 : ℂ) 1)
    (fs : ℕ → ℂ → Pt X) (f : ℂ → Pt X) (u : ℂ → ℝ)
    (hfs : ∀ j, IsHolomorphicDisc (fs j)) (hf : ContinuousOn f O)
    (hconv : letI := L12Aux.inducedMetricSpace X.metric; TendstoLocallyUniformlyOn fs f atTop O)
    (hS : IsCompact S) (hSO : S ⊆ O) (hu : IntegrableOn u S volume)
    (hL1 : Tendsto (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs j z) - u z|) atTop (𝓝 0)) :
    (fun z => immersionPotential X.metric.form F (f z)) =ᵐ[volume.restrict S] u := by
  letI := L12Aux.inducedMetricSpace X.metric
  have hψ : Continuous (immersionPotential X.metric.form F) := L18Aux.continuous_of_smoothFn
    (immersionPotential_smooth X.metric.form (L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm)
  apply ae_eq_of_L1_and_pointwise _ u _
    (fun j => (hψ.comp_continuousOn ((hfs j).continuousOn.mono
      (hSO.trans hOD |>.trans ball_subset_closedBall))).integrableOn_compact hS) hu
    ((hψ.comp_continuousOn (hf.mono hSO)).integrableOn_compact hS) hL1
  filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
  exact hψ.continuousAt.tendsto.comp (hconv.tendsto_at (hSO hz))

theorem ae_on_open_of_ae_on_compacts {O : Set ℂ} (hO : IsOpen O)
    (ν : Measure ℂ) (P : ℂ → Prop)
    (hP : ∀ K : Set ℂ, IsCompact K → K ⊆ O → ∀ᵐ z ∂ν.restrict K, P z) :
    ∀ᵐ z ∂ν.restrict O, P z := by
  letI : LocallyCompactSpace O := hO.locallyCompactSpace
  let E := CompactExhaustion.choice O
  let K : ℕ → Set ℂ := fun j => (Subtype.val : O → ℂ) '' E j
  have hK (j : ℕ) : IsCompact (K j) := (E.isCompact j).image continuous_subtype_val
  have hKO (j : ℕ) : K j ⊆ O := by rintro _ ⟨z, _, rfl⟩; exact z.2
  have hcover : (⋃ j, K j) = O := by
    apply Subset.antisymm (iUnion_subset hKO)
    intro z hz
    let w : O := ⟨z, hz⟩
    obtain ⟨j, hj⟩ := E.exists_superset_of_isCompact (isCompact_singleton : IsCompact ({w} : Set O))
    exact mem_iUnion.mpr ⟨j, w, hj (mem_singleton w), rfl⟩
  rw [← hcover]
  exact (ae_restrict_iUnion_iff K P).mpr (fun j => hP (K j) (hK j) (hKO j))

theorem immersionPotential_limit_ae_on_disc {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (fs : ℕ → ℂ → Pt X) (f : ℂ → Pt X) (u : ℂ → ℝ) (μ : Measure ℂ)
    (hfs : ∀ j, IsHolomorphicDisc (fs j))
    (hf : ContinuousOn f (regularPotentialDomain (ball (0 : ℂ) 1) μ))
    (hconv : letI := L12Aux.inducedMetricSpace X.metric;
      TendstoLocallyUniformlyOn fs f atTop (regularPotentialDomain (ball (0 : ℂ) 1) μ))
    (hlocal : ∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 → IntegrableOn u S volume ∧
      Tendsto (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs j z) - u z|) atTop (𝓝 0))
    (hμ : ∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 → μ S < ⊤) :
    (fun z => immersionPotential X.metric.form F (f z)) =ᵐ[volume.restrict (ball (0 : ℂ) 1)] u := by
  let O := regularPotentialDomain (ball (0 : ℂ) 1) μ
  have ho : IsOpen O := regularPotentialDomain_isOpen isOpen_ball μ hμ
  have hOD : O ⊆ ball (0 : ℂ) 1 := fun _ hz => hz.1
  have haeO : (fun z => immersionPotential X.metric.form F (f z)) =ᵐ[volume.restrict O] u := by
    apply ae_on_open_of_ae_on_compacts ho volume
    intro S hS hSO
    exact immersionPotential_limit_ae_on_compact X hF hImm ho hOD fs f u hfs hf hconv hS hSO
      (hlocal S hS (hSO.trans hOD)).1 (hlocal S hS (hSO.trans hOD)).2
  have hZ := concentrationAtoms_countable isOpen_ball μ hμ
  have hZae : ∀ᵐ z : ℂ ∂volume, z ∉ concentrationAtoms (ball (0 : ℂ) 1) μ := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hZ.measure_zero volume
  have hglobal := (ae_restrict_iff' ho.measurableSet).mp haeO
  filter_upwards [ae_restrict_of_ae hglobal, ae_restrict_of_ae hZae,
    ae_restrict_mem measurableSet_ball] with z he hzZ hzD
  apply he
  exact ⟨hzD, lt_of_not_ge (fun hmass => hzZ ⟨hzD, hmass⟩)⟩

end Yau.NodeProofs.D02Aux
