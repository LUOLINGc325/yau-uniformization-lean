import Yau.Proofs.F03DirichletChartLocal

/-! Unique gluing of the actual supported positive-time interior representatives. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- The single actual supported heat family has a smooth interior
representative, extended by zero outside Ω, representing every time slice.
The local PDE germs are retained for the original total Laplacian. -/
theorem dirichletHeat_exists_globalRepresentative (hn : 0 < n)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    ∃ u : M.Carrier → ℝ → ℝ,
      (∀ a : M.Carrier, ContDiffOn ℝ ∞
        (fun p : Parabolic.Point n => u (chartInv a p.1) p.2)
        ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi 0)) ∧
      (∀ t > 0, (fun y => u y t) =ᵐ[μ.restrict Ω] (dirichletHeat g μ hμ Ω t f : M.Carrier → ℝ)) ∧
      (∀ y ∉ Ω, ∀ t, u y t = 0) ∧
      ∀ (y : M.Carrier), y ∈ Ω → ∀ (t : ℝ), 0 < t →
        ∃ (Q : Set (Parabolic.Point n)) (v : Parabolic.Point n → ℝ),
          IsOpen Q ∧ (chartPt y y,t) ∈ Q ∧ ContDiffOn ℝ ∞ v Q ∧
          (fun p : Parabolic.Point n => u (chartInv y p.1) p.2) =ᶠ[𝓝 (chartPt y y,t)] v ∧
          Parabolic.linearOp Q (scalarHeatChartCoeff g y) (fun _ _ => 0) v (chartPt y y,t) = 0 := by
  classical
  let P := {x : M.Carrier // x ∈ Ω} × {t : ℝ // 0 < t}
  have hLocal (q : P) := dirichletHeat_local_chart_data hn g hK μ hμ Ω hΩ f q.1.val q.1.property q.2.property
  choose O V l r v hO hOc hOt hOΩ hV hVc hVO hz hl hlt htr hv hAE hPDE using hLocal
  let T : P → Set ℝ := fun q => Set.Ioo (l q) (r q)
  have hVt (q : P) : V q ⊆ chartTarget q.1.val :=
    subset_closure.trans ((hVO q).trans (subset_closure.trans (hOt q)))
  let U : P → Set M.Carrier := fun q => scalarChartRegion q.1.val (V q)
  have hUOpen (q : P) : IsOpen (U q) := scalarChartRegion_open q.1.val (hV q) (hVt q)
  have hUSource (q : P) : U q ⊆ (extChartAt (ComplexModel n) q.1.val).source :=
    scalarChartRegion_source q.1.val (hVt q)
  have hUCoords (q : P) {y : M.Carrier} (hy : y ∈ U q) : chartPt q.1.val y ∈ V q :=
    scalarChartRegion_coords q.1.val (hVt q) hy
  have hUΩ (q : P) : U q ⊆ Ω := by
    rintro y ⟨z,hz,rfl⟩
    exact hOΩ q ⟨z,subset_closure (hVO q (subset_closure hz)),rfl⟩
  have hUSelf (q : P) : q.1.val ∈ U q := by
    exact ⟨chartPt q.1.val q.1.val,hz q,(extChartAt (ComplexModel n) q.1.val).left_inv (mem_extChartAt_source q.1.val)⟩
  have hTSelf (q : P) : q.2.val ∈ T q := ⟨hlt q,htr q⟩
  have hTPos (q : P) {s : ℝ} (hs : s ∈ T q) : 0 < s := (hl q).trans hs.1
  let W : P → M.Carrier → ℝ → ℝ := fun q y s => v q (chartPt q.1.val y,s)
  have hWCont (q : P) {s : ℝ} (hs : s ∈ T q) : ContinuousOn (fun y => W q y s) (U q) :=
    (hv q).continuousOn.comp
      (((continuousOn_extChartAt (I := ComplexModel n) q.1.val).mono (hUSource q)).prodMk continuousOn_const)
      (fun y hy => ⟨hVO q (subset_closure (hUCoords q hy)),hs⟩)
  have hWAE (q : P) {s : ℝ} (hs : s ∈ T q) :
      (fun y => W q y s) =ᵐ[μ.restrict (U q)] (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω s f) : M.Carrier → ℝ) :=
    scalarChart_ae_pushforward g μ hμ q.1.val (hV q) (hVt q) (hAE q s hs)
  have : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hAgree (q k : P) {y : M.Carrier} (hyq : y ∈ U q) (hyk : y ∈ U k)
      {s : ℝ} (hsq : s ∈ T q) (hsk : s ∈ T k) : W q y s = W k y s := by
    have hq : (fun z => W q z s) =ᵐ[μ.restrict (U q ∩ U k)]
        (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω s f) : M.Carrier → ℝ) :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hWAE q hsq)
    have hk : (fun z => W k z s) =ᵐ[μ.restrict (U q ∩ U k)]
        (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω s f) : M.Carrier → ℝ) :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hWAE k hsk)
    have hEq : (fun z => W q z s) =ᵐ[μ.restrict (U q ∩ U k)] (fun z => W k z s) := by
      filter_upwards [hq,hk] with z hzq hzk
      exact hzq.trans hzk.symm
    exact Measure.eqOn_open_of_ae_eq hEq ((hUOpen q).inter (hUOpen k))
      ((hWCont q hsq).mono Set.inter_subset_left) ((hWCont k hsk).mono Set.inter_subset_right) ⟨hyq,hyk⟩
  let u : M.Carrier → ℝ → ℝ := fun y t =>
    if hy : y ∈ Ω then if ht : 0 < t then W (⟨y,hy⟩,⟨t,ht⟩) y t else 0 else 0
  have huAgree (q : P) {y : M.Carrier} (hy : y ∈ U q) {s : ℝ} (hs : s ∈ T q) : u y s = W q y s := by
    have hpos := hTPos q hs
    have hyΩ := hUΩ q hy
    have he := hAgree (⟨y,hyΩ⟩,⟨s,hpos⟩) q (hUSelf _) hy (hTSelf _) hs
    simpa only [u,dite_eq_left hyΩ,dite_eq_left hpos] using he
  have huSmooth : ∀ a : M.Carrier, ContDiffOn ℝ ∞
      (fun p : Parabolic.Point n => u (chartInv a p.1) p.2)
      ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi 0) := by
    intro a p hp
    let y := chartInv a p.1
    let q : P := (⟨y,hp.1.2⟩,⟨p.2,hp.2⟩)
    have hyU : y ∈ U q := hUSelf q
    have hsT : p.2 ∈ T q := hTSelf q
    have hTrans : ContDiffAt ℝ ∞ (fun z => chartPt q.1.val (chartInv a z)) p.1 :=
      (chartTransition_contDiffAt a q.1.val hp.1.1 (hUSource q hyU)).restrict_scalars ℝ
    have hMap : ContDiffAt ℝ ∞
        (fun p : Parabolic.Point n => (chartPt q.1.val (chartInv a p.1),p.2)) p :=
      (hTrans.comp p contDiffAt_fst).prodMk contDiffAt_snd
    have hPoint : (chartPt q.1.val y,p.2) ∈ O q ×ˢ T q :=
      ⟨hVO q (subset_closure (hUCoords q hyU)),hsT⟩
    have hComp := ((hv q).contDiffAt (((hO q).prod isOpen_Ioo).mem_nhds hPoint)).comp p hMap
    have hInv : ContinuousAt (fun p : Parabolic.Point n => chartInv a p.1) p :=
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).continuousAt
        ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hp.1.1)).comp continuousAt_fst
    have hNU := hInv.tendsto.eventually ((hUOpen q).mem_nhds hyU)
    have hNT := continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds hsT)
    have hEq : (fun p : Parabolic.Point n => u (chartInv a p.1) p.2) =ᶠ[𝓝 p]
        (fun p => v q (chartPt q.1.val (chartInv a p.1),p.2)) := by
      filter_upwards [hNU,hNT] with p' hy hs
      exact huAgree q hy hs
    exact (hComp.congr_of_eventuallyEq hEq).contDiffWithinAt
  have huAE (t : ℝ) (ht : 0 < t) :
      (fun y => u y t) =ᵐ[μ.restrict Ω] (dirichletHeat g μ hμ Ω t f : M.Carrier → ℝ) := by
    let J : {y : M.Carrier // y ∈ Ω} → P := fun y => (y,⟨t,ht⟩)
    let C : {y : M.Carrier // y ∈ Ω} → Set M.Carrier := fun y => U (J y)
    have hCover : Ω ⊆ ⋃ y, C y := by
      intro y hy
      exact Set.mem_iUnion.mpr ⟨⟨y,hy⟩,hUSelf (J ⟨y,hy⟩)⟩
    obtain ⟨s,hs,hCover⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
      C (fun y => hUOpen (J y)) hCover
    have hUnion : (⋃ y ∈ s, C y) = Ω := by
      apply Set.Subset.antisymm
      · exact Set.iUnion₂_subset (fun y _ => hUΩ (J y))
      · exact hCover
    have hAEUnion : (fun y => u y t) =ᵐ[μ.restrict (⋃ y ∈ s, C y)]
        (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t f) : M.Carrier → ℝ) := by
      apply (ae_eq_restrict_biUnion_iff C hs _ _).2
      intro y _
      filter_upwards [hWAE (J y) (hTSelf (J y)),ae_restrict_mem (hUOpen (J y)).measurableSet]
        with z hz hzU
      exact (huAgree (J y) hzU (hTSelf (J y))).trans hz
    rw [hUnion] at hAEUnion
    have hZ := ae_restrict_of_ae (s := Ω)
      (extendL2_coe μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t f))
    filter_upwards [hAEUnion,hZ,ae_restrict_mem hΩ.measurableSet] with y hy hz hyΩ
    exact hy.trans (hz.trans (Set.indicator_of_mem hyΩ _))
  refine ⟨u,huSmooth,huAE,(fun y hy t => by simp only [u,dite_eq_right hy]),?_⟩
  intro y hy t ht
  let q : P := (⟨y,hy⟩,⟨t,ht⟩)
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


end Yau.Proofs.F03Aux
