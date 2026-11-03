import Yau.LeafProofs.L19HeatRegularityChartTransport

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux

/-- Genuine every-time actual-volume local representatives glue uniquely on any time set, including a closed slab. They agree
 on an arbitrary open manifold region. The original physical trace is
 common BEFORE the chart cover. No heat kernel, weak solver or PDE is a
 premise of this generic gluing argument. -/
theorem glue_smooth_actual_trace
    {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {Ω : Set M.Carrier} (hΩ : IsOpen Ω) (I : Set ℝ)
    {ι : Type*} (c : ι → M.Carrier) (V : ι → Set (Space n))
    (hV : ∀ i, IsOpen (V i)) (hVt : ∀ i, V i ⊆ chartTarget (c i))
    (hVO : ∀ i, scalarChartRegion (c i) (V i) ⊆ Ω)
    (hCover : Ω ⊆ ⋃ i, scalarChartRegion (c i) (V i))
    (v : ι → Point n → ℝ) (hv : ∀ i, ContDiffOn ℝ ∞ (v i) (V i ×ˢ I))
    (A : ℝ → M.Carrier → ℝ)
    (hAE : ∀ i, ∀ t ∈ I, (fun z => v i (z,t)) =ᵐ[volume.restrict (V i)]
      (fun z => A t (chartInv (c i) z))) :
    ∃ u : M.Carrier → ℝ → ℝ,
      (∀ a, ContDiffOn ℝ ∞ (fun p : Point n => u (chartInv a p.1) p.2)
        ((chartTarget a ∩ chartInv a ⁻¹' Ω) ×ˢ I)) ∧
      (∀ t ∈ I, (fun y => u y t) =ᵐ[μ.restrict Ω] A t) ∧
      (∀ i, ∀ y ∈ scalarChartRegion (c i) (V i), ∀ t ∈ I,
        u y t = v i (chartPt (c i) y,t)) ∧
      (∀ y ∉ Ω, ∀ t, u y t = 0) ∧ (∀ y, ∀ t ∉ I, u y t = 0) := by
  classical
  let U := fun i => scalarChartRegion (c i) (V i)
  have hUOpen (i : ι) : IsOpen (U i) := scalarChartRegion_open (c i) (hV i) (hVt i)
  have hUSource (i : ι) : U i ⊆ (extChartAt (ComplexModel n) (c i)).source :=
    scalarChartRegion_source (c i) (hVt i)
  have hUCoords (i : ι) {y : M.Carrier} (hy : y ∈ U i) : chartPt (c i) y ∈ V i :=
    scalarChartRegion_coords (c i) (hVt i) hy
  have hChoice (y : Ω) : ∃ i, y.val ∈ U i := mem_iUnion.mp (hCover y.property)
  choose idx hidx using hChoice
  let W := fun i y t => v i (chartPt (c i) y,t)
  have hWCont (i : ι) {t : ℝ} (ht : t ∈ I) : ContinuousOn (fun y => W i y t) (U i) :=
    (hv i).continuousOn.comp
      (((continuousOn_extChartAt (I := ComplexModel n) (c i)).mono (hUSource i)).prodMk continuousOn_const)
      (fun y hy => ⟨hUCoords i hy,ht⟩)
  have hWAE (i : ι) {t : ℝ} (ht : t ∈ I) :
      (fun y => W i y t) =ᵐ[μ.restrict (U i)] A t :=
    scalarChart_ae_pushforward g μ hμ (c i) (hV i) (hVt i) (hAE i t ht)
  have : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hAgree (i j : ι) {y : M.Carrier} (hyi : y ∈ U i) (hyj : y ∈ U j)
      {t : ℝ} (ht : t ∈ I) : W i y t = W j y t := by
    have hi : (fun z => W i z t) =ᵐ[μ.restrict (U i ∩ U j)] A t :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hWAE i ht)
    have hj : (fun z => W j z t) =ᵐ[μ.restrict (U i ∩ U j)] A t :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hWAE j ht)
    have he : (fun z => W i z t) =ᵐ[μ.restrict (U i ∩ U j)] (fun z => W j z t) := by
      filter_upwards [hi,hj] with z hz₁ hz₂
      exact hz₁.trans hz₂.symm
    exact Measure.eqOn_open_of_ae_eq he ((hUOpen i).inter (hUOpen j))
      ((hWCont i ht).mono inter_subset_left) ((hWCont j ht).mono inter_subset_right) ⟨hyi,hyj⟩
  let u : M.Carrier → ℝ → ℝ := fun y t => if hy : y ∈ Ω then
    if t ∈ I then W (idx ⟨y,hy⟩) y t else 0 else 0
  have huAgree (i : ι) {y : M.Carrier} (hy : y ∈ U i) {t : ℝ} (ht : t ∈ I) : u y t = W i y t := by
    have hyΩ := hVO i hy
    have he := hAgree (idx ⟨y,hyΩ⟩) i (hidx ⟨y,hyΩ⟩) hy ht
    simpa only [u,dif_pos hyΩ,if_pos ht] using he
  have huSmooth : ∀ a, ContDiffOn ℝ ∞ (fun p : Point n => u (chartInv a p.1) p.2)
      ((chartTarget a ∩ chartInv a ⁻¹' Ω) ×ˢ I) := by
    intro a p hp
    let y := chartInv a p.1
    let i := idx ⟨y,hp.1.2⟩
    have hyU : y ∈ U i := hidx ⟨y,hp.1.2⟩
    have hTrans : ContDiffAt ℝ ∞ (fun z => chartPt (c i) (chartInv a z)) p.1 :=
      (chartTransition_contDiffAt a (c i) hp.1.1 (hUSource i hyU)).restrict_scalars ℝ
    have hMap : ContDiffAt ℝ ∞ (fun q : Point n => (chartPt (c i) (chartInv a q.1),q.2)) p :=
      (hTrans.comp p contDiffAt_fst).prodMk contDiffAt_snd
    have hPoint : (chartPt (c i) y,p.2) ∈ V i ×ˢ I := ⟨hUCoords i hyU,hp.2⟩
    have hInv : ContinuousAt (fun q : Point n => chartInv a q.1) p :=
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).continuousAt
        ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hp.1.1)).comp continuousAt_fst
    have hNU := hInv.tendsto.eventually ((hUOpen i).mem_nhds hyU)
    have hNUw : (fun q : Point n => chartInv a q.1) ⁻¹' U i ∈
        𝓝[(chartTarget a ∩ chartInv a ⁻¹' Ω) ×ˢ I] p := mem_nhdsWithin_of_mem_nhds hNU
    have hPre : (fun q : Point n => (chartPt (c i) (chartInv a q.1),q.2)) ⁻¹' (V i ×ˢ I) ∈
        𝓝[(chartTarget a ∩ chartInv a ⁻¹' Ω) ×ˢ I] p := by
      filter_upwards [hNUw,self_mem_nhdsWithin] with q hq hqD
      exact ⟨hUCoords i hq,hqD.2⟩
    have hComp := (hv i _ hPoint).comp_of_preimage_mem_nhdsWithin p hMap.contDiffWithinAt hPre
    have he : (fun q : Point n => u (chartInv a q.1) q.2) =ᶠ[𝓝[(chartTarget a ∩ chartInv a ⁻¹' Ω) ×ˢ I] p]
        (fun q => v i (chartPt (c i) (chartInv a q.1),q.2)) := by
      filter_upwards [hNUw,self_mem_nhdsWithin] with q hq hqD
      exact huAgree i hq hqD.2
    exact hComp.congr_of_eventuallyEq_of_mem he hp
  have huAE (t : ℝ) (ht : t ∈ I) : (fun y => u y t) =ᵐ[μ.restrict Ω] A t := by
    obtain ⟨s,hs,hSubcover⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover U hUOpen hCover
    have hUnion : (⋃ i ∈ s, U i) = Ω := Subset.antisymm
      (iUnion₂_subset (fun i _ => hVO i)) hSubcover
    have hAEUnion : (fun y => u y t) =ᵐ[μ.restrict (⋃ i ∈ s, U i)] A t := by
      apply (ae_eq_restrict_biUnion_iff U hs _ _).2
      intro i _
      filter_upwards [hWAE i ht,ae_restrict_mem (hUOpen i).measurableSet] with y hy hyU
      exact (huAgree i hyU ht).trans hy
    simpa only [hUnion] using hAEUnion
  refine ⟨u,huSmooth,huAE,?_,?_,?_⟩
  · intro i y hy t ht
    exact huAgree i hy ht
  · intro y hy t
    simp only [u,dif_neg hy]
  · intro y t ht
    by_cases hy : y ∈ Ω
    · simp only [u,dif_pos hy,if_neg ht]
    · simp only [u,dif_neg hy]

end Yau.F04Proof
