import Yau.Proofs.F03DirichletEulerConvergence
import Yau.Proofs.F03DirichletStepMarkov

/-! Markov bounds for the single constructed supported heat family, from its actual Euler limit. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The constructed heat preserves every bounded nonnegative interval. -/
theorem dirichletHeat_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O) {t : ℝ} (ht : 0 ≤ t)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 (μ.restrict O))
    (hf : ∀ᵐ x ∂μ.restrict O, 0 ≤ f x ∧ f x ≤ K) :
    ∀ᵐ x ∂μ.restrict O, 0 ≤ dirichletHeat g μ hμ O t f x ∧ dirichletHeat g μ hμ O t f x ≤ K := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [dirichletHeat_zero, one_apply_eq_self] using hf
  · exact dirichletStepResolvent_euler_limit_markov g μ hμ O hO
      (fun k => t / scalarEulerCount k) (fun k => div_pos ht (scalarEulerCount_cast_pos k))
      scalarEulerCount K hK f hf _ (dirichletHeat_euler_apply_tendsto g μ hμ O t ht f)

/-- Signed L∞ contractivity on the actual bounded L² inputs. -/
theorem dirichletHeat_abs_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O) {t : ℝ} (ht : 0 ≤ t)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 (μ.restrict O)) (hf : ∀ᵐ x ∂μ.restrict O, |f x| ≤ K) :
    ∀ᵐ x ∂μ.restrict O, |dirichletHeat g μ hμ O t f x| ≤ K := by
  have hparts := lp_posPart_negPart_bounded f hf
  have hp := dirichletHeat_markov g μ hμ O hO ht K hK (Lp.posPart f) hparts.1
  have hn := dirichletHeat_markov g μ hμ O hO ht K hK (Lp.negPart f) hparts.2
  have heq : dirichletHeat g μ hμ O t f =
      dirichletHeat g μ hμ O t (Lp.posPart f) - dirichletHeat g μ hμ O t (Lp.negPart f) := by
    have h := congrArg (dirichletHeat g μ hμ O t) (lp_posPart_sub_negPart f)
    rwa [map_sub] at h
  filter_upwards [hp, hn, Lp.coeFn_sub (dirichletHeat g μ hμ O t (Lp.posPart f))
    (dirichletHeat g μ hμ O t (Lp.negPart f))] with x hpx hnx hsub
  rw [heq, hsub, Pi.sub_apply]
  exact abs_le.mpr ⟨by linarith only [hpx.1, hnx.2], by linarith only [hpx.2, hnx.1]⟩

end Yau.Proofs.F03Aux
