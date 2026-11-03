import Yau.Proofs.F03WordOperatorContinuity

/-! Genuine norm C-infinity from actual scalar words and their local bounds. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A theorem about actual bounded linear maps, proved from their scalar
derivatives and native mean values; no weak-to-strong smoothness oracle. -/
theorem wordOperator_contDiffOn
    (A : List E → E → H →L[ℝ] ℝ) (F : H → E → ℝ) {Q : Set E} (hQ : IsOpen Q)
    (heval : ∀ w, ∀ x ∈ Q, ∀ f, A w x f = directionalWordDerivative (F f) w x)
    (hF : ∀ f, ContDiffOn ℝ ∞ (F f) Q)
    (hloc : ∀ x ∈ Q, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Q ∧
      ∀ w : List E, ∃ C : ℝ, ∀ y ∈ Metric.ball x r, ‖A w y‖ ≤ C)
    (w : List E) : ContDiffOn ℝ ∞ (A w) Q := by
  have hA := wordOperator_continuousOn A F hQ heval hF hloc
  have hD := wordOperatorDerivative_continuousOn A F Q heval hA
  have hd (w : List E) (x : E) (hx : x ∈ Q) :
      HasFDerivAt (A w) (wordOperatorDerivative A F Q heval w x) x := by
    exact hasFDerivAt_operator_of_apply (A w) (wordOperatorDerivative A F Q heval w) hQ
      (fun f z hz => wordOperatorDerivative_hasFDerivAt_apply A F hQ heval hF w hz f)
      hx ((hD w).continuousAt (hQ.mem_nhds hx))
  rw [contDiffOn_infty]
  intro m
  induction m generalizing w with
  | zero => exact contDiffOn_zero.mpr (hA w)
  | succ m ih =>
    have hdiff : DifferentiableOn ℝ (A w) Q := fun x hx =>
      (hd w x hx).differentiableAt.differentiableWithinAt
    have happ (v : E) : ContDiffOn ℝ (m : ℕ∞ω)
        (fun x => fderivWithin ℝ (A w) Q x v) Q := by
      apply (ih (v::w)).congr
      intro x hx
      rw [(hd w x hx).hasFDerivWithinAt.fderivWithin (hQ.uniqueDiffWithinAt hx)]
      exact wordOperatorDerivative_apply A F Q heval w hx v
    simpa only [Nat.cast_add,Nat.cast_one] using
      (contDiffOn_succ_of_fderiv_apply hdiff (by simp) happ)

end Yau.Proofs.F03Aux
