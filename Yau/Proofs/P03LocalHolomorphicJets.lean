import Yau.Proofs.P03HolomorphicL2Decay
import Yau.Proofs.P03HolomorphicCutoffExtension
import Yau.LeafProofs.L17HolomorphicRegularity

open scoped Topology ContDiff
open Set Filter MeasureTheory ContinuousMultilinearMap

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- The decay criterion is local and concludes the actual native complex
jets, at every requested order. -/
theorem complex_jets_zero_of_L2_decay {U : Set (ComplexVector n)} (hU : IsOpen U)
    (f : ComplexVector n → ℂ) (hf : DifferentiableOn ℂ f U)
    (a : ComplexVector n) (ha : a ∈ U) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hL2 : ∀ t : ℝ, 0 < t → t < R →
      (∫ z in Metric.closedBall a t, ‖f z‖ ^ 2) ≤ D * t ^ (2 * (n + k + 1))) :
    ∀ j ≤ k, iteratedFDeriv ℂ j f a = 0 := by
  obtain ⟨F, hFc, hfc, hgerm⟩ := exists_continuous_compact_model hU hf.continuousOn ha
  have hV : U ∩ {z | F z = f z} ∈ 𝓝 a := inter_mem (hU.mem_nhds ha) hgerm
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  let ρ := min (R / 2) (δ / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρR : ρ < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρδ : ρ < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hHF : DifferentiableOn ℂ F (Metric.ball a ρ) :=
    (hf.mono (fun z hz => (hδV (Metric.ball_subset_ball hρδ.le hz)).1)).congr
      (fun z hz => (hδV (Metric.ball_subset_ball hρδ.le hz)).2)
  have hdecay : ∀ t : ℝ, 0 < t → t < ρ →
      (∫ z in Metric.closedBall a t, ‖F z‖ ^ 2) ≤ D * t ^ (2 * (n + k + 1)) := by
    intro t ht htρ
    have heq : (∫ z in Metric.closedBall a t, ‖F z‖ ^ 2) =
        ∫ z in Metric.closedBall a t, ‖f z‖ ^ 2 := by
      apply setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
      intro z hz
      change ‖F z‖ ^ 2 = ‖f z‖ ^ 2
      rw [(hδV (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (htρ.trans hρδ)))).2]
    rw [heq]
    exact hL2 t ht (htρ.trans hρR)
  have hz := real_jets_zero_of_L2_decay F hFc hfc a ρ hρ hHF k D hD hdecay
  have hreg := (Yau.LeafProofs.L17Holomorphic.contDiffOn_of_complexDiff hU hf a ha).contDiffAt
    (hU.mem_nhds ha)
  intro j hj
  have hreal : iteratedFDeriv ℝ j f a = 0 :=
    ((hgerm.iteratedFDeriv ℝ j).self_of_nhds).symm.trans (hz j hj)
  have hres : (iteratedFDeriv ℂ j f a).restrictScalars ℝ = iteratedFDeriv ℝ j f a :=
    (hreg.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).restrictScalars_iteratedFDeriv
  ext v
  have he := congrArg (fun T : ComplexVector n [×j]→L[ℝ] ℂ => T v) (hres.trans hreal)
  change (iteratedFDeriv ℂ j f a) v = 0 at he
  exact he

end Yau.NodeProofs.P03Aux
