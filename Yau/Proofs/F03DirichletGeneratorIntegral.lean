import Yau.Proofs.F03DirichletGenerator
import Yau.Proofs.F03L2FilterConvergence

/-! The exact integral initial-generator limit for the actual supported heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual pointwise representatives have the exact L² norm integral. -/
theorem lintegral_sq_eq_ofReal_lp_norm {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (v : Lp ℝ 2 ν) {r : α → ℝ} (hr : v =ᵐ[ν] r) :
    (∫⁻ x, ENNReal.ofReal (|r x| ^ 2) ∂ν) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  have heq : ENNReal.ofReal (∫ x, inner ℝ (v x) (v x) ∂ν) =
      ∫⁻ x, ENNReal.ofReal ((v x) ^ 2) ∂ν := by
    simp only [RCLike.inner_apply,conj_trivial,← pow_two]
    exact ofReal_integral_eq_lintegral_ofReal (Lp.memLp v).integrable_sq
      (ae_of_all _ (fun x => sq_nonneg _))
  rw [heq]
  apply lintegral_congr_ae
  filter_upwards [hr] with x hx
  simp only [hx,sq_abs]

variable {n : ℕ} {M : ComplexManifold n}

/-- Both directions of the literal ENNReal integral criterion, with the
actual supported semigroup in place of its future kernel representation.
The graph and normalization are exactly the registered scalar graph. -/
theorem scalarFriedrichsPair_iff_heat_generator_integral (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (f w : M.Carrier → ℝ)
    (hf : ScalarL2 (μ.restrict O) f) (hw : ScalarL2 (μ.restrict O) w) :
    ScalarFriedrichsPair g.form μ O f w ↔
      Tendsto (fun t : ℝ => ∫⁻ x in O, ENNReal.ofReal
        (|((dirichletHeat g μ hμ O t (scalarToLp hf) x - f x) / t) + w x| ^ 2) ∂μ)
          (𝓝[>] 0) (𝓝 0) := by
  rw [scalarFriedrichsPair_iff_heat_generator g μ hμ O hO f w hf hw]
  let F := fun t : ℝ => t⁻¹ • (dirichletHeat g μ hμ O t (scalarToLp hf) - scalarToLp hf) + scalarToLp hw
  have heq (t : ℝ) :
      (∫⁻ x in O, ENNReal.ofReal
        (|((dirichletHeat g μ hμ O t (scalarToLp hf) x - f x) / t) + w x| ^ 2) ∂μ) =
        ENNReal.ofReal (‖F t‖ ^ 2) := by
    apply lintegral_sq_eq_ofReal_lp_norm
    filter_upwards [Lp.coeFn_add (t⁻¹ • (dirichletHeat g μ hμ O t (scalarToLp hf) - scalarToLp hf)) (scalarToLp hw),
      Lp.coeFn_smul t⁻¹ (dirichletHeat g μ hμ O t (scalarToLp hf) - scalarToLp hf),
      Lp.coeFn_sub (dirichletHeat g μ hμ O t (scalarToLp hf)) (scalarToLp hf),
      scalarToLp_coe hf,scalarToLp_coe hw] with x ha hs hd hfx hwx
    change F t x = _
    dsimp only [F]
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.sub_apply,hfx,hwx,div_eq_mul_inv,mul_comm]
  simp_rw [heq]
  exact (tendsto_ofReal_norm_sq_iff (𝓝[>] (0 : ℝ)) F).symm

end Yau.Proofs.F03Aux
