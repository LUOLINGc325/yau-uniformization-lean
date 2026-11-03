import Yau.Proofs.F03WordOperatorDerivative

/-! Uniform boundedness and actual mean values give norm continuity of jets. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Locally bounded actual word-source operators are norm continuous.
The full next-derivative norm is proved by native Banach-Steinhaus. -/
theorem wordOperator_continuousOn
    (A : List E → E → H →L[ℝ] ℝ) (F : H → E → ℝ) {Q : Set E} (hQ : IsOpen Q)
    (heval : ∀ w, ∀ x ∈ Q, ∀ f, A w x f = directionalWordDerivative (F f) w x)
    (hF : ∀ f, ContDiffOn ℝ ∞ (F f) Q)
    (hloc : ∀ x ∈ Q, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Q ∧
      ∀ w : List E, ∃ C : ℝ, ∀ y ∈ Metric.ball x r, ‖A w y‖ ≤ C)
    (w : List E) : ContinuousOn (A w) Q := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro x hx
  obtain ⟨r,hr,hrQ,hbound⟩ := hloc x hx
  let D := wordOperatorDerivative A F Q heval w
  have hp (v : E) : ∃ C : ℝ, ∀ y : Metric.ball x r, ‖D y.val v‖ ≤ C := by
    obtain ⟨C,hC⟩ := hbound (v::w)
    refine ⟨C,?_⟩
    intro y
    rw [wordOperatorDerivative_apply A F Q heval w (hrQ y.property)]
    exact hC y.val y.property
  obtain ⟨C,hC⟩ := banach_steinhaus (g := fun y : Metric.ball x r => D y.val) hp
  have hC' : 0 ≤ max 0 C := le_max_left _ _
  have hder (f : H) (y : E) (hy : y ∈ Metric.ball x r) :
      HasFDerivAt (fun z => A w z f) ((D y).flip f) y :=
    wordOperatorDerivative_hasFDerivAt_apply A F hQ heval hF w (hrQ hy) f
  have hDb (f : H) (y : E) (hy : y ∈ Metric.ball x r) :
      ‖(D y).flip f‖ ≤ max 0 C * ‖f‖ := by
    exact ((D y).flip.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (by
        rw [ContinuousLinearMap.opNorm_flip]
        exact (hC ⟨y,hy⟩).trans (le_max_right _ _)) (norm_nonneg f))
  have hLip : LipschitzOnWith ⟨max 0 C,hC'⟩ (A w) (Metric.ball x r) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro y hy z hz
    exact operator_norm_image_sub_le (A w) (fun f y => (D y).flip f)
      (convex_ball x r) hder hC' hDb hz hy
  exact (hLip.continuousOn.continuousAt (Metric.ball_mem_nhds x hr)).continuousWithinAt

end Yau.Proofs.F03Aux
