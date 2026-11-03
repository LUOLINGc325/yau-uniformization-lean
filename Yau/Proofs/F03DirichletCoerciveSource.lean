import Yau.Proofs.F03DirichletClassicalDerivative

/-! The actual coercive (A+1) source is the computed inverse heat factor. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

theorem dirichletHeatEnergy_coercive_source (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier)
    (t : ℝ) (f : Lp ℝ 2 (μ.restrict Ω)) (v : DirichletEnergy g μ hμ Ω) :
    inner ℝ (dirichletHeatEnergy g μ hμ Ω t f) v =
      inner ℝ (dirichletHeatInverse g μ hμ Ω t f) (dirichletL2 g μ hμ Ω v) := by
  change inner ℝ ((dirichletL2 g μ hμ Ω).adjoint _) v = _
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem dirichletHeatInverse_ae_classical_split (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    {σ t : ℝ} (hσ : 0 < σ) (hσt : σ < t) :
    (dirichletHeatInverse g μ hμ Ω t f : M.Carrier → ℝ) =ᵐ[μ.restrict Ω]
      (fun x => dirichletClassicalHeat g hK μ hμ Ω hΩ f x t-
        dirichletClassicalHeat g hK μ hμ Ω hΩ (dirichletHeatDerivativeOperator g μ hμ Ω (t-σ) f) x σ) := by
  let k := dirichletHeatDerivativeOperator g μ hμ Ω (t-σ) f
  have htime : (t-σ)+σ=t := by ring
  have hfac := congrArg (fun A : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 (μ.restrict Ω) => A f)
    (dirichletHeatDerivative_left_factor g μ hμ Ω (sub_pos.mpr hσt) hσ.le)
  have hD : dirichletHeat g μ hμ Ω t f-dirichletHeatInverse g μ hμ Ω t f =
      dirichletHeat g μ hμ Ω σ k := by
    simpa only [htime,k,dirichletHeatDerivativeOperator,sub_apply,mul_apply_eq_comp] using hfac
  have hInv : dirichletHeatInverse g μ hμ Ω t f =
      dirichletHeat g μ hμ Ω t f-dirichletHeat g μ hμ Ω σ k := by
    calc
      _ = dirichletHeat g μ hμ Ω t f-
          (dirichletHeat g μ hμ Ω t f-dirichletHeatInverse g μ hμ Ω t f) := by abel
      _ = _ := congrArg (fun z => dirichletHeat g μ hμ Ω t f-z) hD
  filter_upwards [Lp.coeFn_sub (dirichletHeat g μ hμ Ω t f) (dirichletHeat g μ hμ Ω σ k),
    dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f (hσ.trans hσt),
    dirichletClassicalHeat_ae g hK μ hμ Ω hΩ k hσ] with x hsub hu hk
  rw [hInv,hsub,Pi.sub_apply,← hu,← hk]

theorem dirichletHeatInverse_ae_laplacian (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω)) {t : ℝ} (ht : 0 < t) :
    (dirichletHeatInverse g μ hμ Ω t f : M.Carrier → ℝ) =ᵐ[μ.restrict Ω]
      (fun x => dirichletClassicalHeat g hK μ hμ Ω hΩ f x t-
        laplacian g.form (fun y => dirichletClassicalHeat g hK μ hμ Ω hΩ f y t) x) := by
  filter_upwards [dirichletHeatInverse_ae_classical_split g hK μ hμ Ω hΩ f (half_pos ht) (half_lt_self ht),
    ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  rw [← dirichletClassicalHeat_laplacian_split g hK μ hμ Ω hΩ f x hxΩ (half_pos ht) (half_lt_self ht)] at hx
  exact hx

end Yau.Proofs.F03Aux
