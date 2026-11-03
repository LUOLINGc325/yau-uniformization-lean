import Yau.LeafProofs.L21LocalChart

/-! A fixed inverse ball for the one coordinate map furnished by L21. -/

noncomputable section
open scoped Topology ContDiff NNReal

namespace Yau.Proofs.C04ChartsAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Nontrivial E]

theorem approximates_id_of_fderiv_close (F : E → E) (hF : ContDiff ℝ ∞ F)
    (hclose : ∀ x ∈ Metric.ball (0 : E) (1 / 2 : ℝ),
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) :
    ApproximatesLinearOn F (ContinuousLinearMap.id ℝ E)
      (Metric.ball 0 (1 / 2 : ℝ)) (1 / 4 : ℝ≥0) := by
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_fderiv_le'
    (fun x _ => hF.differentiable (by simp) x) hclose (convex_ball 0 _) hy hx

theorem norm_le_of_approximates_id (F : E → E) (hzero : F 0 = 0)
    (happrox : ApproximatesLinearOn F (ContinuousLinearMap.id ℝ E)
      (Metric.ball 0 (1 / 2 : ℝ)) (1 / 4 : ℝ≥0))
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    ‖x‖ ≤ (4 / 3 : ℝ) * ‖F x‖ := by
  have hh := happrox x hx 0 (Metric.mem_ball_self (by norm_num))
  simp only [hzero, sub_zero, ContinuousLinearMap.id_apply, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat] at hh
  have htri : ‖x‖ ≤ ‖F x‖ + ‖F x - x‖ := by
    calc
      ‖x‖ = ‖F x - (F x - x)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

theorem inverse_on_fixed_ball (F : E → E) (hF : ContDiff ℝ ∞ F)
    (hzero : F 0 = 0)
    (hclose : ∀ x ∈ Metric.ball (0 : E) (1 / 2 : ℝ),
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) :
    ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = F ∧ e.source = Metric.ball 0 (1 / 2 : ℝ) ∧
      Metric.closedBall (0 : E) (3 / 16 : ℝ) ⊆ e.target ∧
      e.symm 0 = 0 ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ w ∈ e.target, ‖e.symm w‖ ≤ (4 / 3 : ℝ) * ‖w‖ := by
  let idE := ContinuousLinearEquiv.refl ℝ E
  have happrox : ApproximatesLinearOn F (idE : E →L[ℝ] E)
      (Metric.ball 0 (1 / 2 : ℝ)) (1 / 4 : ℝ≥0) :=
    approximates_id_of_fderiv_close F hF hclose
  have ht : Subsingleton E ∨
      (1 / 4 : ℝ≥0) < ‖(idE.symm : E →L[ℝ] E)‖₊⁻¹ := by
    right
    norm_num [idE]
  let e := happrox.toOpenPartialHomeomorph F (Metric.ball 0 (1 / 2 : ℝ)) ht Metric.isOpen_ball
  have he : (e : E → E) = F := rfl
  have hsource : e.source = Metric.ball 0 (1 / 2 : ℝ) := rfl
  have h0 : (0 : E) ∈ e.source := by rw [hsource]; exact Metric.mem_ball_self (by norm_num)
  have htarget : Metric.closedBall (0 : E) (3 / 16 : ℝ) ⊆ e.target := by
    have hball : Metric.closedBall (0 : E) (1 / 4 : ℝ) ⊆ Metric.ball 0 (1 / 2 : ℝ) :=
      Metric.closedBall_subset_ball (by norm_num)
    have H := happrox.closedBall_subset_target ht Metric.isOpen_ball
      (by norm_num : (0 : ℝ) ≤ 1 / 4) hball
    change Metric.closedBall (0 : E) (3 / 16 : ℝ) ⊆ F '' Metric.ball 0 (1 / 2 : ℝ)
    convert H using 1 <;> norm_num [idE, hzero]
  have hinv : ContDiffOn ℝ ∞ e.symm e.target := by
    intro w hw
    have hx : e.symm w ∈ Metric.ball (0 : E) (1 / 2 : ℝ) :=
      hsource ▸ e.map_target hw
    obtain ⟨D, hD⟩ := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one
      (fderiv ℝ F (e.symm w)) (lt_of_le_of_lt (hclose _ hx) (by norm_num))
    have hd : HasFDerivAt e (D : E →L[ℝ] E) (e.symm w) := by
      rw [he, hD]
      exact (hF.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hw hd (he ▸ hF.contDiffAt)).contDiffWithinAt
  refine ⟨e, he, hsource, htarget, ?_, hinv, ?_⟩
  · calc
      e.symm 0 = e.symm (e 0) := by rw [he, hzero]
      _ = 0 := e.left_inv h0
  · intro w hw
    have H := norm_le_of_approximates_id F hzero happrox (hsource ▸ e.map_target hw)
    have hew : F (e.symm w) = w := by rw [← he]; exact e.right_inv hw
    rwa [hew] at H

end Yau.Proofs.C04ChartsAux
