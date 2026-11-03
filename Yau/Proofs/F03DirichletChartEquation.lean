import Yau.Proofs.F03DirichletCompactJet
import Yau.Proofs.F03DirichletClassicalPairing

/-! The actual heat equation in every interior chart, at every point. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletClassicalChartHeat_equation (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (f : Lp ℝ 2 (μ.restrict Ω)) (p : Parabolic.Point n)
    (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) :
    Parabolic.linearOp ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
      (scalarHeatChartCoeff g a) (fun _ _ => 0)
      (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f) p = 0 := by
  let F := dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f
  let Q := {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)
  have hQ : IsOpen Q := (dirichletChartInterior_open Ω hΩ a).prod isOpen_Ioi
  obtain ⟨O,hO,hpO,hOD,hOc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (dirichletChartInterior_open Ω hΩ a) (singleton_subset_iff.mpr hp.1)
  have hOt : closure O ⊆ chartTarget a := fun z hz => (hOD hz).1
  have hOΩ : chartInv a '' O ⊆ Ω := by
    rintro y ⟨z,hz,rfl⟩
    exact (hOD (subset_closure hz)).2
  obtain ⟨V,hV,hpV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton hO hpO
  have hl : 0 < p.2/2 := half_pos hp.2
  have hlt : p.2/2 < p.2 := half_lt_self hp.2
  have htr : p.2 < p.2+1 := by linarith
  obtain ⟨v,hv,hAE,hClass⟩ := dirichletHeat_chartClassicalRepresentative
    (complexManifold_dimension_pos M) g hK μ hμ Ω hΩ.measurableSet a hO hOc hOt hOΩ
    hV hVc hVO hl (hlt.trans htr) f
  have hVt : closure V ⊆ chartTarget a := hVO.trans (subset_closure.trans hOt)
  have hVQ : V ×ˢ Ioo (p.2/2) (p.2+1) ⊆ Q := by
    intro q hq
    have hqO := hVO (subset_closure hq.1)
    exact ⟨⟨(subset_closure.trans hOt) hqO,hOΩ ⟨q.1,hqO,rfl⟩⟩,hl.trans hq.2.1⟩
  have heq : EqOn F v (V ×ˢ Ioo (p.2/2) (p.2+1)) := by
    intro q hq
    have huCont : ContinuousOn (fun z => F (z,q.2)) V :=
      ((dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a f).continuousOn.mono hVQ).comp
        (continuous_id.prodMk continuous_const).continuousOn (fun z hz => ⟨hz,hq.2⟩)
    have hvCont : ContinuousOn (fun z => v (z,q.2)) V := hv.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hVO (subset_closure hz),hq.2⟩)
    have huAE := (dirichletClassicalHeat_chart_ae g hK μ hμ Ω hΩ f a hV hVc hVt
      (hl.trans hq.2.1)).trans (scalarEnergy_chartRestrictionCLM_coe g μ hμ a hV hVc hVt _)
    exact Measure.eqOn_open_of_ae_eq (huAE.trans (hAE q.2 hq.2).symm) hV huCont hvCont hq.1
  have hGerm : F =ᶠ[𝓝 p] v := by
    filter_upwards [(hV.prod isOpen_Ioo).mem_nhds
      (show p ∈ V ×ˢ Ioo (p.2/2) (p.2+1) from ⟨hpV (mem_singleton _),hlt,htr⟩)] with q hq
    exact heq hq
  have hpO' : p ∈ O ×ˢ Ioo (p.2/2) (p.2+1) :=
    ⟨hpO (mem_singleton _),hlt,htr⟩
  exact (linearOp_congr_open_sets hQ (hO.prod isOpen_Ioo)
    (scalarHeatChartCoeff g a) (fun _ _ => 0) hp hpO' hGerm).trans (hClass p hpO')

end Yau.Proofs.F03Aux
