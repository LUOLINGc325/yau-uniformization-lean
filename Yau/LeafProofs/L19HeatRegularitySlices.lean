import Yau.LeafProofs.L19HeatRegularityWeakEquation

/-! Upgrading genuine spacetime representatives to every time slice. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A smooth spacetime function has a continuous actual L² slice path on
every relatively compact spatial subdomain. The path is constructed from
its genuine functions; continuity is proved by actual L² dominated convergence. -/
theorem scalarSmoothSlice_exists_continuousLp
    {O V : Set (ComplexVector n)} (hO : IsOpen O) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O) {l r : ℝ}
    {v : Parabolic.Point n → ℝ} (hv : ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r)) :
    ∃ A : ℝ → Lp ℝ 2 (volume.restrict V), ContinuousOn A (Set.Ioo l r) ∧
      ∀ t ∈ Set.Ioo l r, A t =ᵐ[volume.restrict V] (fun z => v (z,t)) := by
  have hVvol : volume V < (⊤ : ENNReal) := lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top
  have : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hVvol.ne
  let F : ℝ → ComplexVector n → ℝ := fun t z => if t ∈ Set.Ioo l r then v (z,t) else 0
  have hF (t : ℝ) : MemLp (F t) 2 (volume.restrict V) := by
    by_cases ht : t ∈ Set.Ioo l r
    · have hc : ContinuousOn (fun z => v (z,t)) (closure V) :=
        hv.continuousOn.comp (continuousOn_id.prodMk continuousOn_const) (fun z hz => ⟨hVO hz,ht⟩)
      obtain ⟨C,hC⟩ := hVc.bddAbove_image hc.norm
      have hm : AEStronglyMeasurable (F t) (volume.restrict V) := by
        simpa only [F,ite_eq_left ht] using (hc.mono subset_closure).aestronglyMeasurable hV.measurableSet
      apply MemLp.of_bound hm C
      filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
      simpa only [F,ite_eq_left ht] using hC ⟨z,subset_closure hz,rfl⟩
    · simpa only [F,ite_eq_right ht,Pi.zero_def] using (MemLp.zero : MemLp (fun _ : ComplexVector n => (0 : ℝ)) 2 (volume.restrict V))
  let A : ℝ → Lp ℝ 2 (volume.restrict V) := fun t => (hF t).toLp (F t)
  refine ⟨A,?_,?_⟩
  · intro t ht
    apply ContinuousAt.continuousWithinAt
    let c := (l+t)/2
    let e := (t+r)/2
    have hct : c < t := by dsimp only [c]; linarith [ht.1]
    have hte : t < e := by dsimp only [e]; linarith [ht.2]
    have hce : Set.Icc c e ⊆ Set.Ioo l r := by
      intro s hs
      dsimp only [c,e] at hs
      constructor <;> linarith [ht.1,ht.2,hs.1,hs.2]
    have hKc : IsCompact (closure V ×ˢ Set.Icc c e) := hVc.prod isCompact_Icc
    have hKQ : closure V ×ˢ Set.Icc c e ⊆ O ×ˢ Set.Ioo l r :=
      Set.prod_mono hVO hce
    obtain ⟨C,hC⟩ := hKc.bddAbove_image (hv.continuousOn.mono hKQ).norm
    have hbound : ∀ᶠ s in 𝓝 t, ∀ᵐ z ∂volume.restrict V, ‖F s z‖ ≤ C := by
      filter_upwards [Ioo_mem_nhds hct hte] with s hs
      filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
      have hsI := hce (Set.Ioo_subset_Icc_self hs)
      simpa only [F,ite_eq_left hsI] using hC ⟨(z,s),⟨subset_closure hz,Set.Ioo_subset_Icc_self hs⟩,rfl⟩
    have hlim : ∀ᵐ z ∂volume.restrict V, Tendsto (fun s => F s z) (𝓝 t) (𝓝 (F t z)) := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
      have hvt : ContinuousAt (fun s => v (z,s)) t :=
        (hv.continuousOn.continuousAt ((hO.prod isOpen_Ioo).mem_nhds
          ⟨hVO (subset_closure hz),ht⟩)).comp (continuous_const.prodMk continuous_id).continuousAt
      have heq : (fun s => F s z) =ᶠ[𝓝 t] (fun s => v (z,s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        simp only [F,ite_eq_left hs]
      rw [show F t z = v (z,t) by simp only [F,ite_eq_left ht],tendsto_congr' heq]
      exact hvt.tendsto
    exact scalarL2_tendsto_of_dominated A (fun s => (hF s).coeFn_toLp) (hF t) (memLp_const C) hbound hlim
  · intro t ht
    simpa only [A,F,ite_eq_left ht] using (hF t).coeFn_toLp

/-- Equality of the smooth representative and the actual heat slice,
initially only for almost every time, holds for every time on every
relatively compact inner chart domain. -/
theorem scalarHeat_chart_smoothSlice_every_time (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O V : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) {l r : ℝ} (hl : 0 < l) (f : Lp ℝ 2 μ)
    {v : Parabolic.Point n → ℝ} (hv : ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r))
    (hAE : ∀ᵐ t ∂volume.restrict (Set.Ioo l r), (fun z => v (z,t)) =ᵐ[volume.restrict O]
      scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f)) :
    ∀ t ∈ Set.Ioo l r, (fun z => v (z,t)) =ᵐ[volume.restrict V]
      (fun z => (scalarHeatFamily g μ hμ t f) (chartInv x z)) := by
  obtain ⟨A,hAc,hA⟩ := scalarSmoothSlice_exists_continuousLp hO hV hVc hVO hv
  let R := scalarEnergy_chartRestrictionCLM g μ hμ x hV hVc
    (hVO.trans (subset_closure.trans hOt))
  let B := fun t => R (scalarHeatFamily g μ hμ t f)
  have hBc : ContinuousOn B (Set.Ioo l r) := fun t ht =>
    (scalarHeat_chartValues_continuousAt g μ hμ x hV hVc
      (hVO.trans (subset_closure.trans hOt)) (hl.trans ht.1) f).continuousWithinAt
  have hAB : A =ᵐ[volume.restrict (Set.Ioo l r)] B := by
    filter_upwards [hAE,ae_restrict_mem measurableSet_Ioo] with t ht htI
    apply Lp.ext
    have hOV : V ⊆ O := subset_closure.trans hVO
    have hvO := ae_restrict_of_ae_restrict_of_subset hOV ht
    have hOuter := ae_restrict_of_ae_restrict_of_subset hOV
      (scalarEnergy_chartRestrictionCLM_coe g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f))
    have hInner := scalarEnergy_chartRestrictionCLM_coe g μ hμ x hV hVc
      (hVO.trans (subset_closure.trans hOt)) (scalarHeatFamily g μ hμ t f)
    filter_upwards [hA t htI,hvO,hOuter,hInner] with z hAz hvz hoz hiz
    exact hAz.trans (hvz.trans (hoz.trans hiz.symm))

  have hAll := Measure.eqOn_open_of_ae_eq hAB isOpen_Ioo hAc hBc
  intro t ht
  have he := hAll ht
  have hLpAE := Lp.ext_iff.mp he
  filter_upwards [hA t ht,hLpAE,scalarEnergy_chartRestrictionCLM_coe g μ hμ x hV hVc
    (hVO.trans (subset_closure.trans hOt)) (scalarHeatFamily g μ hμ t f)] with z hAz hEq hR
  exact hAz.symm.trans (hEq.trans hR)

end Yau.LeafProofs.L19Aux
