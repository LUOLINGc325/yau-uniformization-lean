import Yau.Proofs.F03ParabolicTimeShift
import Yau.Proofs.F03DirichletChartEquation
import Yau.LeafProofs.L19HeatRegularityEllipticity

/-! Genuine compact classical heat cylinders, with actual ellipticity before all sources. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletClassicalHeat_shifted_cylinder (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (K : Set (Space n)) (hKc : IsCompact K)
    (hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω})
    {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    ∃ lam upper : ℝ, Elliptic (cylinder K 0 T) (scalarHeatChartCoeff g a) lam upper ∧
      ∀ f : Lp ℝ 2 (μ.restrict Ω),
      C2 (cylinder K 0 T) (positiveTimeShift s (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f)) ∧
      ∀ p ∈ cylinder K 0 T,
        linearOp (cylinder K 0 T) (scalarHeatChartCoeff g a) (fun _ _ => 0)
          (positiveTimeShift s (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f)) p=0 := by
  obtain ⟨lam,upper,hEll⟩ := scalarHeatChartCoeff_elliptic g a hKc
    (fun z hz => (hKQ hz).1) (Icc (0 : ℝ) T)
  refine ⟨lam,upper,hEll,?_⟩
  intro f
  refine ⟨positiveTimeShift_C2 (dirichletChartInterior_open Ω hΩ a)
    (dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a f) hs hT hKQ,?_⟩
  intro p hp
  have hEq := positiveTimeShift_linearOp (dirichletChartInterior_open Ω hΩ a)
    (dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a f)
    (scalarHeatChartCoeff g a) hs hT hKQ p hp
  change linearOp (cylinder K 0 T) (scalarHeatChartCoeff g a) (fun _ _ => 0)
    (positiveTimeShift s (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f)) p = _ at hEq
  exact hEq.trans (dirichletClassicalChartHeat_equation g hK μ hμ Ω hΩ a f (p.1,s+p.2)
    ⟨hKQ hp.1,add_pos_of_pos_of_nonneg hs hp.2.1⟩)

end Yau.Proofs.F03Aux
