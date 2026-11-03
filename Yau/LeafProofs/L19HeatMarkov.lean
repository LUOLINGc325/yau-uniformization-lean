import Yau.LeafProofs.L19HeatMarkovEuler
import Yau.LeafProofs.L19ScalarMarkovBounds
import Mathlib.MeasureTheory.Function.LpOrder

/-! Markov and signed bounded-function estimates for the actual scalar heat.
The Euler limit is proved in operator norm before it is used here. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The constructed heat preserves every bounded nonnegative interval. -/
theorem scalarHeatFamily_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 ≤ t)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K) :
    ∀ᵐ x ∂μ, 0 ≤ scalarHeatFamily g μ hμ t f x ∧ scalarHeatFamily g μ hμ t f x ≤ K := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [scalarHeatFamily_zero, one_apply_eq_self] using hf
  · exact scalarResolvent_euler_limit_markov g μ hμ
      (fun k => t / scalarEulerCount k) (fun k => div_pos ht (scalarEulerCount_cast_pos k))
      scalarEulerCount K hK f hf _ (scalarHeatFamily_euler_apply_tendsto g μ hμ t ht f)

/-- Signed L∞ contractivity on the actual bounded L² inputs. -/
theorem scalarHeatFamily_abs_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 ≤ t)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, |f x| ≤ K) :
    ∀ᵐ x ∂μ, |scalarHeatFamily g μ hμ t f x| ≤ K := by
  have hparts := lp_posPart_negPart_bounded f hf
  have hp := scalarHeatFamily_markov g μ hμ ht K hK (Lp.posPart f) hparts.1
  have hn := scalarHeatFamily_markov g μ hμ ht K hK (Lp.negPart f) hparts.2
  have heq : scalarHeatFamily g μ hμ t f =
      scalarHeatFamily g μ hμ t (Lp.posPart f) - scalarHeatFamily g μ hμ t (Lp.negPart f) := by
    have h := congrArg (scalarHeatFamily g μ hμ t) (lp_posPart_sub_negPart f)
    rwa [map_sub] at h
  filter_upwards [hp, hn, Lp.coeFn_sub (scalarHeatFamily g μ hμ t (Lp.posPart f))
    (scalarHeatFamily g μ hμ t (Lp.negPart f))] with x hpx hnx hsub
  rw [heq, hsub, Pi.sub_apply]
  exact abs_le.mpr ⟨by linarith only [hpx.1, hnx.2], by linarith only [hpx.2, hnx.1]⟩

end Yau.LeafProofs.L19Aux
