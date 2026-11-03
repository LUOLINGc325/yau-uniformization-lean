import Yau.LeafProofs.L19HeatRegularityChartTransport

/-! Global gluing of the every-time actual heat representatives. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Every-time actual-volume slice identities uniquely glue the internally
constructed local classical charts to a globally smooth heat representative.
The last conclusion retains its genuine local classical PDE germs. -/
theorem scalarHeat_exists_globalRepresentative (hn : 0 < n)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    ∃ u : M.Carrier → ℝ → ℝ, SmoothSpaceTime u (Set.Ioi 0) ∧
      (∀ t > 0, (fun y => u y t) =ᵐ[μ] (scalarHeatFamily g μ hμ t f : M.Carrier → ℝ)) ∧
      ∀ (y : M.Carrier) (t : ℝ), 0 < t →
        ∃ (Q : Set (Parabolic.Point n)) (v : Parabolic.Point n → ℝ),
          IsOpen Q ∧ (chartPt y y,t) ∈ Q ∧ ContDiffOn ℝ ∞ v Q ∧
          (fun p : Parabolic.Point n => u (chartInv y p.1) p.2) =ᶠ[𝓝 (chartPt y y,t)] v ∧
          Parabolic.linearOp Q (scalarHeatChartCoeff g y) (fun _ _ => 0) v (chartPt y y,t) = 0 := by
  classical
  let P := M.Carrier × {t : ℝ // 0 < t}
  have hLocal (q : P) := scalarHeat_local_chart_data hn g hK μ hμ f q.1 q.2.property
  choose O V l r v hO hOc hOt hV hVc hVO hz hl hlt htr hv hAE hPDE using hLocal
  let T : P → Set ℝ := fun q => Set.Ioo (l q) (r q)
  have hVt (q : P) : V q ⊆ chartTarget q.1 :=
    subset_closure.trans ((hVO q).trans (subset_closure.trans (hOt q)))
  let U : P → Set M.Carrier := fun q => scalarChartRegion q.1 (V q)
  have hUOpen (q : P) : IsOpen (U q) := scalarChartRegion_open q.1 (hV q) (hVt q)
  have hUSource (q : P) : U q ⊆ (extChartAt (ComplexModel n) q.1).source :=
    scalarChartRegion_source q.1 (hVt q)
  have hUCoords (q : P) {y : M.Carrier} (hy : y ∈ U q) : chartPt q.1 y ∈ V q :=
    scalarChartRegion_coords q.1 (hVt q) hy
  have hUSelf (q : P) : q.1 ∈ U q := by
    exact ⟨chartPt q.1 q.1,hz q,(extChartAt (ComplexModel n) q.1).left_inv (mem_extChartAt_source q.1)⟩
  have hTSelf (q : P) : q.2.val ∈ T q := ⟨hlt q,htr q⟩
  have hTPos (q : P) {s : ℝ} (hs : s ∈ T q) : 0 < s := (hl q).trans hs.1
  let W : P → M.Carrier → ℝ → ℝ := fun q y s => v q (chartPt q.1 y,s)
  have hWCont (q : P) {s : ℝ} (hs : s ∈ T q) : ContinuousOn (fun y => W q y s) (U q) :=
    (hv q).continuousOn.comp
      (((continuousOn_extChartAt (I := ComplexModel n) q.1).mono (hUSource q)).prodMk continuousOn_const)
      (fun y hy => ⟨hVO q (subset_closure (hUCoords q hy)),hs⟩)
  have hWAE (q : P) {s : ℝ} (hs : s ∈ T q) :
      (fun y => W q y s) =ᵐ[μ.restrict (U q)] (scalarHeatFamily g μ hμ s f : M.Carrier → ℝ) :=
    scalarChart_ae_pushforward g μ hμ q.1 (hV q) (hVt q) (hAE q s hs)
  have : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hAgree (q k : P) {y : M.Carrier} (hyq : y ∈ U q) (hyk : y ∈ U k)
      {s : ℝ} (hsq : s ∈ T q) (hsk : s ∈ T k) : W q y s = W k y s := by
    have hq : (fun z => W q z s) =ᵐ[μ.restrict (U q ∩ U k)]
        (scalarHeatFamily g μ hμ s f : M.Carrier → ℝ) :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hWAE q hsq)
    have hk : (fun z => W k z s) =ᵐ[μ.restrict (U q ∩ U k)]
        (scalarHeatFamily g μ hμ s f : M.Carrier → ℝ) :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hWAE k hsk)
    have hEq : (fun z => W q z s) =ᵐ[μ.restrict (U q ∩ U k)] (fun z => W k z s) := by
      filter_upwards [hq,hk] with z hzq hzk
      exact hzq.trans hzk.symm
    exact Measure.eqOn_open_of_ae_eq hEq ((hUOpen q).inter (hUOpen k))
      ((hWCont q hsq).mono Set.inter_subset_left) ((hWCont k hsk).mono Set.inter_subset_right) ⟨hyq,hyk⟩
  let u : M.Carrier → ℝ → ℝ := fun y t => if ht : 0 < t then W (y,⟨t,ht⟩) y t else 0
  have huAgree (q : P) {y : M.Carrier} (hy : y ∈ U q) {s : ℝ} (hs : s ∈ T q) : u y s = W q y s := by
    have hpos := hTPos q hs
    have he := hAgree (y,⟨s,hpos⟩) q (hUSelf _) hy (hTSelf _) hs
    simpa only [u,dite_eq_left hpos] using he
  have huSmooth : SmoothSpaceTime u (Set.Ioi 0) := by
    intro a p hp
    let y := chartInv a p.1
    let q : P := (y,⟨p.2,hp.2⟩)
    have hyU : y ∈ U q := hUSelf q
    have hsT : p.2 ∈ T q := hTSelf q
    have hTrans : ContDiffAt ℝ ∞ (fun z => chartPt q.1 (chartInv a z)) p.1 :=
      (chartTransition_contDiffAt a q.1 hp.1 (hUSource q hyU)).restrict_scalars ℝ
    have hMap : ContDiffAt ℝ ∞
        (fun p : Parabolic.Point n => (chartPt q.1 (chartInv a p.1),p.2)) p :=
      (hTrans.comp p contDiffAt_fst).prodMk contDiffAt_snd
    have hPoint : (chartPt q.1 y,p.2) ∈ O q ×ˢ T q :=
      ⟨hVO q (subset_closure (hUCoords q hyU)),hsT⟩
    have hComp := ((hv q).contDiffAt (((hO q).prod isOpen_Ioo).mem_nhds hPoint)).comp p hMap
    have hInv : ContinuousAt (fun p : Parabolic.Point n => chartInv a p.1) p :=
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).continuousAt
        ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hp.1)).comp continuousAt_fst
    have hNU := hInv.tendsto.eventually ((hUOpen q).mem_nhds hyU)
    have hNT := continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds hsT)
    have hEq : (fun p : Parabolic.Point n => u (chartInv a p.1) p.2) =ᶠ[𝓝 p]
        (fun p => v q (chartPt q.1 (chartInv a p.1),p.2)) := by
      filter_upwards [hNU,hNT] with p' hy hs
      exact huAgree q hy hs
    exact (hComp.congr_of_eventuallyEq hEq).contDiffWithinAt
  have huAE (t : ℝ) (ht : 0 < t) :
      (fun y => u y t) =ᵐ[μ] (scalarHeatFamily g μ hμ t f : M.Carrier → ℝ) := by
    let J : M.Carrier → P := fun y => (y,⟨t,ht⟩)
    let C : M.Carrier → Set M.Carrier := fun y => U (J y)
    have hCover : (Set.univ : Set M.Carrier) ⊆ ⋃ y, C y := by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y,hUSelf (J y)⟩
    obtain ⟨s,hs,hCover⟩ := isLindelof_univ.elim_countable_subcover C (fun y => hUOpen (J y)) hCover
    have hUnion : (⋃ y ∈ s, C y) = (Set.univ : Set M.Carrier) :=
      Set.Subset.antisymm (Set.subset_univ _) hCover
    have hAEUnion : (fun y => u y t) =ᵐ[μ.restrict (⋃ y ∈ s, C y)]
        (scalarHeatFamily g μ hμ t f : M.Carrier → ℝ) := by
      apply (ae_eq_restrict_biUnion_iff C hs _ _).2
      intro y _
      filter_upwards [hWAE (J y) (hTSelf (J y)),ae_restrict_mem (hUOpen (J y)).measurableSet]
        with z hz hzU
      exact (huAgree (J y) hzU (hTSelf (J y))).trans hz
    simpa only [hUnion,Measure.restrict_univ] using hAEUnion
  refine ⟨u,huSmooth,huAE,?_⟩
  intro y t ht
  let q : P := (y,⟨t,ht⟩)
  let p : Parabolic.Point n := (chartPt y y,t)
  have hpV : p ∈ V q ×ˢ T q := ⟨hz q,hTSelf q⟩
  have hpO : p ∈ O q ×ˢ T q := ⟨hVO q (subset_closure (hz q)),hTSelf q⟩
  have hEq : (fun p : Parabolic.Point n => u (chartInv y p.1) p.2) =ᶠ[𝓝 p] v q := by
    filter_upwards [((hV q).prod isOpen_Ioo).mem_nhds hpV] with p' hp'
    have hzT := hVt q hp'.1
    have hyU : chartInv y p'.1 ∈ U q := ⟨p'.1,hp'.1,rfl⟩
    have he := huAgree q hyU hp'.2
    change u (chartInv y p'.1) p'.2 = v q p'
    rw [he]
    change v q (chartPt y (chartInv y p'.1),p'.2) = v q p'
    have hInv : chartPt y (chartInv y p'.1) = p'.1 := (extChartAt (ComplexModel n) y).right_inv hzT
    rw [hInv]
  exact ⟨O q ×ˢ T q,v q,(hO q).prod isOpen_Ioo,hpO,hv q,hEq,hPDE q p hpO⟩

end Yau.LeafProofs.L19Aux
