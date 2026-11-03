import Yau.Proofs.F03DirichletKernelSplit
import Yau.Proofs.F03DirichletClassicalEquation

/-! The original scalar heat equation of the single actual Riesz kernel. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- A fixed positive time split gives a fixed-source classical heat germ,
so the actual kernel solves the original total-Laplacian equation. -/
theorem dirichletKernelCandidate_hasDerivAt (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {b : ℝ} (hb : 0 < b)
    (x y : M.Carrier) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    HasDerivAt (fun t => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y)
      (laplacian g.form (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ b z y) x) b := by
  let σ := b/2
  have hσ : 0 < σ := half_pos hb
  have hσb : σ < b := half_lt_self hb
  let v := dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy σ hσ
  have hd : HasDerivAt (fun r => dirichletClassicalHeat g hK μ hμ Ω hΩ v x (r-σ))
      (laplacian g.form (fun z => dirichletClassicalHeat g hK μ hμ Ω hΩ v z (b-σ)) x) b := by
    have h := (dirichletClassicalHeat_hasDerivAt g hK μ hμ Ω hΩ v x hx (sub_pos.mpr hσb)).comp b
      ((hasDerivAt_id b).sub_const σ)
    simpa only [Function.comp_def,id_eq,mul_one,one_mul] using h
  have heq : (fun r => dirichletKernelCandidate g hK μ hμ Ω hΩ r x y) =ᶠ[𝓝 b]
      (fun r => dirichletClassicalHeat g hK μ hμ Ω hΩ v x (r-σ)) := by
    filter_upwards [eventually_gt_nhds hσb] with r hr
    exact congrFun (dirichletKernelCandidate_split_heat g hK μ hμ Ω hΩ hσ hr y hy) x
  have hSlice : (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ b z y) =
      (fun z => dirichletClassicalHeat g hK μ hμ Ω hΩ v z (b-σ)) :=
    dirichletKernelCandidate_split_heat g hK μ hμ Ω hΩ hσ hσb y hy
  rw [hSlice]
  exact hd.congr_of_eventuallyEq heq

end Yau.Proofs.F03Aux
