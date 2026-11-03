import Yau.Proofs.F03DirichletRieszSmooth

/-! The actual Hilbert-valued evaluation field is continuous on the manifold interior. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def dirichletRieszVectorAt (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (t : ℝ) (ht : 0 < t) (x : M.Carrier) :
    Lp ℝ 2 (μ.restrict Ω) := by
  classical
  exact if hx : x ∈ Ω then dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht else 0

theorem dirichletRieszVectorAt_inner (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (t : ℝ) (ht : 0 < t) (x : M.Carrier) (hx : x ∈ Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    inner ℝ (dirichletRieszVectorAt g hK μ hμ Ω hΩ t ht x) f =
      dirichletClassicalHeat g hK μ hμ Ω hΩ f x t := by
  classical
  simp only [dirichletRieszVectorAt,dif_pos hx,dirichletHeatEvaluationVector_inner]

theorem dirichletRieszVectorAt_continuousOn (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (t : ℝ) (ht : 0 < t) :
    ContinuousOn (dirichletRieszVectorAt g hK μ hμ Ω hΩ t ht) Ω := by
  intro x hx
  have hsrc : x ∈ (extChartAt (ComplexModel n) x).source := mem_extChartAt_source x
  have hsrcOpen : IsOpen (extChartAt (ComplexModel n) x).source := by
    rw [extChartAt_source]
    exact (chartAt (ComplexVector n) x).open_source
  have hpt : ContinuousAt (chartPt x) x :=
    (continuousOn_extChartAt (I := ComplexModel n) x).continuousAt (hsrcOpen.mem_nhds hsrc)
  have hinv : chartInv x (chartPt x x)=x := (extChartAt (ComplexModel n) x).left_inv hsrc
  have hp : (chartPt x x,t) ∈ {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} ×ˢ Ioi (0 : ℝ) :=
    ⟨⟨mem_extChartAt_target x,by rwa [hinv]⟩,ht⟩
  have hChart : ContinuousAt (dirichletChartRieszVector g hK μ hμ Ω hΩ x) (chartPt x x,t) :=
    (dirichletChartRieszVector_smooth g hK μ hμ Ω hΩ x).continuousOn.continuousAt
      (((dirichletChartInterior_open Ω hΩ x).prod isOpen_Ioi).mem_nhds hp)
  have hComp : ContinuousAt (fun y => dirichletChartRieszVector g hK μ hμ Ω hΩ x (chartPt x y,t)) x :=
    hChart.comp (f := fun y : M.Carrier => (chartPt x y,t)) (hpt.prodMk continuousAt_const)
  have hEq : (fun y => dirichletChartRieszVector g hK μ hμ Ω hΩ x (chartPt x y,t)) =ᶠ[𝓝 x]
      dirichletRieszVectorAt g hK μ hμ Ω hΩ t ht := by
    filter_upwards [hsrcOpen.mem_nhds hsrc,hΩ.mem_nhds hx] with y hysrc hy
    have hyinv : chartInv x (chartPt x y)=y := (extChartAt (ComplexModel n) x).left_inv hysrc
    have hyp : (chartPt x y,t) ∈ {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} ×ˢ Ioi (0 : ℝ) :=
      ⟨⟨(extChartAt (ComplexModel n) x).map_source hysrc,by rwa [hyinv]⟩,ht⟩
    apply ext_inner_right ℝ
    intro f
    rw [dirichletChartRieszVector_inner g hK μ hμ Ω hΩ x (chartPt x y,t) hyp f,
      dirichletRieszVectorAt_inner g hK μ hμ Ω hΩ t ht y hy f]
    simp only [dirichletClassicalChartHeat,hyinv]
  exact (hComp.congr_of_eventuallyEq (Filter.EventuallyEq.symm hEq)).continuousWithinAt

end Yau.Proofs.F03Aux
