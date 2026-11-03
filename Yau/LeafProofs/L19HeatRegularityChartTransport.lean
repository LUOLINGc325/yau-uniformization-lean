import Yau.LeafProofs.L19HeatRegularityInterior
import Yau.LeafProofs.L03ChartMeasure

/-! Actual-volume transport and genuine local classical heat charts. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual manifold open region corresponding to a chart subdomain. -/
def scalarChartRegion (x : M.Carrier) (V : Set (ComplexVector n)) : Set M.Carrier := chartInv x '' V

theorem scalarChartRegion_open (x : M.Carrier) {V : Set (ComplexVector n)}
    (hV : IsOpen V) (hVt : V ⊆ chartTarget x) : IsOpen (scalarChartRegion x V) := by
  change IsOpen ((chartAt (ComplexVector n) x).symm '' V)
  apply (chartAt (ComplexVector n) x).symm.isOpen_image_of_subset_source hV
  intro z hz
  have hh := hVt hz
  rw [chartTarget,extChartAt_target] at hh
  exact hh.1

theorem scalarChartRegion_source (x : M.Carrier) {V : Set (ComplexVector n)}
    (hVt : V ⊆ chartTarget x) :
    scalarChartRegion x V ⊆ (extChartAt (ComplexModel n) x).source := by
  rintro y ⟨z,hz,rfl⟩
  exact (extChartAt (ComplexModel n) x).map_target (hVt hz)

theorem scalarChartRegion_coords (x : M.Carrier) {V : Set (ComplexVector n)}
    (hVt : V ⊆ chartTarget x) {y : M.Carrier} (hy : y ∈ scalarChartRegion x V) : chartPt x y ∈ V := by
  obtain ⟨z,hz,rfl⟩ := hy
  have heq : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv (hVt hz)
  rw [heq]
  exact hz

/-- Unweighted chart AE slice identities push to the actual Riemannian
volume on the corresponding actual manifold region. -/
theorem scalarChart_ae_pushforward (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {V : Set (ComplexVector n)} (hV : IsOpen V) (hVt : V ⊆ chartTarget x)
    {v : ComplexVector n → ℝ} {f : M.Carrier → ℝ}
    (hAE : v =ᵐ[volume.restrict V] (fun z => f (chartInv x z))) :
    (fun y => v (chartPt x y)) =ᵐ[μ.restrict (scalarChartRegion x V)] f := by
  have hfull : ∀ᵐ z ∂volume, z ∈ V → v z = f (chartInv x z) :=
    (ae_restrict_iff' hV.measurableSet).mp hAE
  have htarget : ∀ᵐ z ∂(lebesgueC n).restrict (chartTarget x), z ∈ V → v z = f (chartInv x z) := by
    rw [lebesgueC_eq_volume]
    exact ae_restrict_of_ae hfull
  have hphysical := (L03.realChartPtExtension_quasiMeasurePreserving g.form μ hμ x).ae htarget
  have hphysical' := ae_restrict_of_ae_restrict_of_subset (scalarChartRegion_source x hVt) hphysical
  filter_upwards [hphysical',ae_restrict_mem (scalarChartRegion_open x hV hVt).measurableSet] with y hy hyU
  have hys := scalarChartRegion_source x hVt hyU
  have hyV := scalarChartRegion_coords x hVt hyU
  have hext : L03.realChartPtExtension x y = chartPt x y := by
    simp only [L03.realChartPtExtension,ite_eq_left hys]
  rw [hext] at hy
  have hh := hy hyV
  rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hys)] at hh
  exact hh

/-- At every genuine positive spacetime point, all local chart data and
its classical solution are constructed internally from the actual heat. -/
theorem scalarHeat_local_chart_data (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    ∃ (O V : Set (ComplexVector n)) (l r : ℝ) (v : Parabolic.Point n → ℝ),
      IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ chartTarget x ∧
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ O ∧ chartPt x x ∈ V ∧
      0 < l ∧ l < t ∧ t < r ∧ ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r) ∧
      (∀ s ∈ Set.Ioo l r, (fun z => v (z,s)) =ᵐ[volume.restrict V]
        (fun z => (scalarHeatFamily g μ hμ s f) (chartInv x z))) ∧
      ∀ p ∈ O ×ˢ Set.Ioo l r,
        Parabolic.linearOp (O ×ˢ Set.Ioo l r) (scalarHeatChartCoeff g x) (fun _ _ => 0) v p = 0 := by
  obtain ⟨O,hO,hxO,hOt,hOc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (isOpen_extChartAt_target (I := ComplexModel n) x)
    (Set.singleton_subset_iff.mpr (mem_extChartAt_target x))
  obtain ⟨V,hV,hxV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton hO hxO
  have hl : 0 < t / 2 := half_pos ht
  have hlt : t / 2 < t := half_lt_self ht
  have htr : t < t + 1 := by linarith
  obtain ⟨v,hv,hAE,hClass⟩ := scalarHeat_chartClassicalRepresentative hn g hK μ hμ x hO hOc hOt
    hV hVc hVO hl (hlt.trans htr) f
  exact ⟨O,V,t/2,t+1,v,hO,hOc,hOt,hV,hVc,hVO,hxV (Set.mem_singleton _),hl,hlt,htr,hv,hAE,hClass⟩

end Yau.LeafProofs.L19Aux
