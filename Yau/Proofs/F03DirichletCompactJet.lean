import Yau.Proofs.F03DirectionalLinearity
import Yau.Proofs.F03DirichletCompactValue

/-! Actual algebraic source-linear finite directional jets on compact cylinders. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def dirichletClassicalChartHeat (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (f : Lp ℝ 2 (μ.restrict Ω)) (p : Parabolic.Point n) : ℝ :=
  dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv a p.1) p.2

theorem dirichletClassicalChartHeat_smooth (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    ContDiffOn ℝ ∞ (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f)
      ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) :=
  dirichletClassicalHeat_smooth g hK μ hμ Ω hΩ f a

/-- Genuine local derivatives of the constructed heat give an algebraic
linear map into C(K), with boundedness still to be proved by compact tests. -/
def dirichletCompactHeatJet (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (K : Set (Parabolic.Point n)) [CompactSpace K]
    (hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
    (w : List (Parabolic.Point n)) : Lp ℝ 2 (μ.restrict Ω) →ₗ[ℝ] C(K,ℝ) where
  toFun f := compactContinuousRestriction K
    (directionalWordDerivative (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f) w)
    ((directionalWordDerivative_contDiffOn
      ((dirichletChartInterior_open Ω hΩ a).prod isOpen_Ioi)
      (dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a f) w).continuousOn.mono hKQ)
  map_add' f k := by
    ext p
    let F := dirichletClassicalChartHeat g hK μ hμ Ω hΩ a
    let Q := {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)
    have hQ : IsOpen Q := (dirichletChartInterior_open Ω hΩ a).prod isOpen_Ioi
    have heq : F (f+k) =ᶠ[𝓝 p.val] (fun q => F f q+F k q) := by
      filter_upwards [hQ.mem_nhds (hKQ p.property)] with q hq
      exact dirichletClassicalHeat_add g hK μ hμ Ω hΩ f k hq.2 (chartInv a q.1) hq.1.2
    change directionalWordDerivative (F (f+k)) w p.val =
      directionalWordDerivative (F f) w p.val + directionalWordDerivative (F k) w p.val
    rw [(directionalWordDerivative_eventuallyEq heq w).eq_of_nhds]
    exact directionalWordDerivative_add_on hQ
      (dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a f)
      (dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a k) w (hKQ p.property)
  map_smul' c f := by
    ext p
    let F := dirichletClassicalChartHeat g hK μ hμ Ω hΩ a
    let Q := {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)
    have hQ : IsOpen Q := (dirichletChartInterior_open Ω hΩ a).prod isOpen_Ioi
    have heq : F (c • f) =ᶠ[𝓝 p.val] (fun q => c*F f q) := by
      filter_upwards [hQ.mem_nhds (hKQ p.property)] with q hq
      exact dirichletClassicalHeat_smul g hK μ hμ Ω hΩ c f hq.2 (chartInv a q.1) hq.1.2
    change directionalWordDerivative (F (c • f)) w p.val = c*directionalWordDerivative (F f) w p.val
    rw [(directionalWordDerivative_eventuallyEq heq w).eq_of_nhds,directionalWordDerivative_const_mul]

end Yau.Proofs.F03Aux
