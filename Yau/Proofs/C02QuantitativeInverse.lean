import Yau.Proofs.C02NearIdentityApproximation

/-! An actual near-identity map has an inverse on a fixed receiving ball.
The radius is numerical and does not come from a qualitative inverse germ. -/

noncomputable section
open Set
open scoped NNReal ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixed_ball_inverse (f : E → E) (R : ℝ) (hR : 0 < R)
    (hf : ContDiff ℝ ∞ f)
    (hClose : ∀ x ∈ Metric.ball (0 : E) R,
      ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧
      e.source = Metric.ball (0 : E) R ∧
      Metric.closedBall (f 0) (3 * R / 8) ⊆ e.target := by
  let I := ContinuousLinearEquiv.refl ℝ E
  have hApprox : ApproximatesLinearOn f (I : E →L[ℝ] E)
      (Metric.ball 0 R) (1 / 4 : ℝ≥0) :=
    approximates_identity_of_fderiv_close (convex_ball (0 : E) R)
      (fun x _ => hf.differentiable (by simp) x) hClose
  have hc : Subsingleton E ∨ (1 / 4 : ℝ≥0) < ‖(I.symm : E →L[ℝ] E)‖₊⁻¹ := by
    by_cases hE : Subsingleton E
    · exact Or.inl hE
    · let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
      right
      norm_num [I, ContinuousLinearMap.nnnorm_id]
  let e := hApprox.toOpenPartialHomeomorph f (Metric.ball 0 R) hc Metric.isOpen_ball
  refine ⟨e, rfl, rfl, ?_⟩
  by_cases hE : Subsingleton E
  · let := hE
    intro y _
    change y ∈ f '' Metric.ball (0 : E) R
    exact ⟨0, by simpa only [Metric.mem_ball, dist_self] using hR, Subsingleton.elim _ _⟩
  · let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hSmall : Metric.closedBall (0 : E) (R / 2) ⊆ Metric.ball (0 : E) R := by
      intro x hx
      exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
    have hh := hApprox.closedBall_subset_target hc Metric.isOpen_ball
      (show 0 ≤ R / 2 by positivity) hSmall
    have hRadius : ((‖(I.symm : E →L[ℝ] E)‖₊⁻¹ : ℝ≥0) - (1 / 4 : ℝ≥0) : ℝ) * (R / 2) =
        3 * R / 8 := by norm_num [I, ContinuousLinearMap.nnnorm_id]; ring
    rw [hRadius] at hh
    exact hh

end Yau.Blueprint.C02Proof
