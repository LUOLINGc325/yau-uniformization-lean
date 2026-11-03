import Yau.Proofs.F03DirichletWordEvaluation
import Yau.Proofs.F03WordOperatorSmooth
import Yau.Proofs.F03DirichletEvaluation

/-! Norm C-infinity of the actual source evaluator and its actual Riesz vector. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletChartWordOperator_smooth (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier) (w : List (Parabolic.Point n)) :
    ContDiffOn ℝ ∞ (dirichletChartWordOperator g hK μ hμ Ω hΩ a w)
      ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) := by
  exact wordOperator_contDiffOn (dirichletChartWordOperator g hK μ hμ Ω hΩ a)
    (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a)
    ((dirichletChartInterior_open Ω hΩ a).prod isOpen_Ioi)
    (fun w p hp f => dirichletChartWordOperator_apply g hK μ hμ Ω hΩ a w p hp f)
    (fun f => dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a f)
    (fun p hp => dirichletChartWordOperator_local_bound g hK μ hμ Ω hΩ a p hp) w

/-- This is the actual Riesz map of the actual bounded source evaluator.
Its norm smoothness is a theorem, not a supplied weak regularity flag. -/
def dirichletChartRieszVector (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (p : Parabolic.Point n) : Lp ℝ 2 (μ.restrict Ω) :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 (μ.restrict Ω))).symm
    (dirichletChartWordOperator g hK μ hμ Ω hΩ a [] p)

theorem dirichletChartRieszVector_inner (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (p : Parabolic.Point n)
    (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    inner ℝ (dirichletChartRieszVector g hK μ hμ Ω hΩ a p) f =
      dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f p := by
  rw [dirichletChartRieszVector,InnerProductSpace.toDual_symm_apply,
    dirichletChartWordOperator_apply g hK μ hμ Ω hΩ a [] p hp]
  rfl

theorem dirichletChartRieszVector_eq (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (p : Parabolic.Point n)
    (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) :
    dirichletChartRieszVector g hK μ hμ Ω hΩ a p =
      dirichletHeatEvaluationVector g hK μ hμ Ω hΩ (chartInv a p.1) hp.1.2 p.2 hp.2 := by
  apply ext_inner_right ℝ
  intro f
  rw [dirichletChartRieszVector_inner g hK μ hμ Ω hΩ a p hp f,
    dirichletHeatEvaluationVector_inner]
  rfl

theorem dirichletChartRieszVector_smooth (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (dirichletChartRieszVector g hK μ hμ Ω hΩ a)
      ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) := by
  exact (InnerProductSpace.toDual ℝ (Lp ℝ 2 (μ.restrict Ω))).symm.contDiff.comp_contDiffOn
    (dirichletChartWordOperator_smooth g hK μ hμ Ω hΩ a [])

end Yau.Proofs.F03Aux
