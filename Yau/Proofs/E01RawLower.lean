import Yau.Proofs.E01FlowDual

/-! The initial circle-mean inequality implies the actual raw bound.
The circle-mean input is the separate Chern calculation; this lemma is conditional only. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ} {X : KahlerManifold n}

theorem envelopeRaw_lower_of_initial_circle_mean
    {o : Pt X} {h : Flow X} {U P ρ : STF X} (hloc : LocalizedFlow X o h U P ρ)
    (hmean : ∀ (f : ℂ → Pt X) (ξd : ℂ → Covector n), IsCotangentDisc f ξd →
      dualNorm X.metric.form (f 0) (ξd 0) ≤
        circleAverage (fun θ => dualNorm X.metric.form
          (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))))
    (T : ℝ) (y : Pt X) (ξ : Covector n) (s : ℝ) :
    (dualNorm X.metric.form y ξ : EReal) ≤ envelopeRaw h T y ξ s := by
  unfold envelopeRaw
  refine le_iInf fun f => le_iInf fun ξd => le_iInf fun w => le_iInf fun had => ?_
  rcases had with ⟨hs, _hsT, hd, hw, hf, hξ, _hw0, _ht⟩
  have hcircle (θ : ℝ) : Complex.exp (θ * Complex.I) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
  have he : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I)) := by fun_prop
  have hg : Continuous (fun θ : ℝ => dualNorm X.metric.form
      (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))) :=
    (cotangentDisc_dualNorm_contDiffOn X.metric (f := fun ζ => (f ζ, ξd ζ)) hd).continuousOn.comp_continuous he hcircle
  have hh : Continuous (fun θ : ℝ => dualNorm (h (s * Real.exp (2 * (w (Complex.exp (θ * Complex.I))).re)))
      (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))) :=
    (localized_disc_cost_contDiffOn hloc hd hw s hs).continuousOn.comp_continuous he hcircle
  have havg : circleAverage (fun θ => dualNorm X.metric.form
      (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))) ≤
      circleAverage (fun θ => dualNorm (h (s * Real.exp (2 * (w (Complex.exp (θ * Complex.I))).re)))
        (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))) := by
    unfold circleAverage
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hg.intervalIntegrable _ _) (hh.intervalIntegrable _ _)
    intro θ _
    exact localized_initial_dualNorm_le hloc _ (mul_pos hs (Real.exp_pos _)).le _ _
  have hm := hmean f ξd hd
  rw [hf, hξ] at hm
  exact EReal.coe_le_coe_iff.mpr (hm.trans havg)

end Yau.NodeProofs.E01Aux
