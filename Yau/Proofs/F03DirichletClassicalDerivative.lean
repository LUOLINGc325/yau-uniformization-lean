import Yau.Proofs.F03DirichletDerivativeFactor
import Yau.Proofs.F03DirichletEvaluation
import Yau.Proofs.F03DirichletClassicalEquation

/-! Actual fixed positive-time smoothing of the computed generator source. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletClassicalHeat_split_hasDerivAt (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (x : M.Carrier) (hx : x ∈ Ω) {σ t : ℝ} (hσ : 0 < σ) (hσt : σ < t) :
    HasDerivAt (dirichletClassicalHeat g hK μ hμ Ω hΩ f x)
      (dirichletClassicalHeat g hK μ hμ Ω hΩ
        (dirichletHeatDerivativeOperator g μ hμ Ω (t-σ) f) x σ) t := by
  let L := dirichletHeatEvaluation g hK μ hμ Ω hΩ x hx σ hσ
  have hd := L.hasFDerivAt.comp_hasDerivAt (t-σ)
    (dirichletHeat_apply_hasDerivAt g μ hμ Ω (sub_pos.mpr hσt) f)
  have hd' : HasDerivAt (fun a => L (dirichletHeat g μ hμ Ω (a-σ) f))
      (L (dirichletHeatDerivativeOperator g μ hμ Ω (t-σ) f)) t := by
    have h := hd.comp t ((hasDerivAt_id t).sub_const σ)
    simpa only [Function.comp_def,id_eq,mul_one,dirichletHeatDerivativeOperator,sub_apply] using h
  have hEq : dirichletClassicalHeat g hK μ hμ Ω hΩ f x =ᶠ[𝓝 t]
      (fun a => L (dirichletHeat g μ hμ Ω (a-σ) f)) := by
    filter_upwards [eventually_gt_nhds hσt] with a ha
    change dirichletClassicalHeat g hK μ hμ Ω hΩ f x a =
      dirichletClassicalHeat g hK μ hμ Ω hΩ (dirichletHeat g μ hμ Ω (a-σ) f) x σ
    have htime : σ+(a-σ)=a := by ring
    simpa only [htime] using dirichletClassicalHeat_semigroup g hK μ hμ Ω hΩ f hσ
      (sub_pos.mpr ha).le x hx
  exact hd'.congr_of_eventuallyEq hEq

theorem dirichletClassicalHeat_laplacian_split (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (x : M.Carrier) (hx : x ∈ Ω) {σ t : ℝ} (hσ : 0 < σ) (hσt : σ < t) :
    laplacian g.form (fun y => dirichletClassicalHeat g hK μ hμ Ω hΩ f y t) x =
      dirichletClassicalHeat g hK μ hμ Ω hΩ (dirichletHeatDerivativeOperator g μ hμ Ω (t-σ) f) x σ :=
  (dirichletClassicalHeat_hasDerivAt g hK μ hμ Ω hΩ f x hx (hσ.trans hσt)).unique
    (dirichletClassicalHeat_split_hasDerivAt g hK μ hμ Ω hΩ f x hx hσ hσt)

end Yau.Proofs.F03Aux
