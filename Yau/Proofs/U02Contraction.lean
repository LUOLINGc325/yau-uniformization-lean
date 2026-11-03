import Mathlib

/-! A quantitative onto statement for the actual normalized map. The
native nonlinear-right-inverse theorem supplies the convergent iteration;
the right inverse used here is literally the identity, also in dimension zero. -/

open scoped Topology NNReal
open Metric Set

noncomputable section
namespace Yau.NodeProofs.U02ContractionAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_preimage_of_small_derivative (T : E → E) (A Ai : E →L[ℂ] E)
    (hleft : Ai.comp A = ContinuousLinearMap.id ℂ E)
    (hright : A.comp Ai = ContinuousLinearMap.id ℂ E)
    {O : Set E} (hO : IsOpen O) (hT : DifferentiableOn ℂ T O) (hT0 : T 0 = 0)
    {R : ℝ} (hR : 0 < R) (hball : closedBall (0 : E) R ⊆ O)
    (hD : ∀ z ∈ closedBall (0 : E) R,
      ‖Ai.comp (fderiv ℂ T z - A)‖ ≤ 1 / 4)
    (w : E) (hw : ‖Ai w‖ ≤ R / 2) :
    ∃ z ∈ closedBall (0 : E) R, T z = w := by
  let S := Ai ∘ T
  have hSd : ∀ z ∈ closedBall (0 : E) R, DifferentiableAt ℂ S z := by
    intro z hz
    exact Ai.differentiableAt.comp z ((hT z (hball hz)).differentiableAt (hO.mem_nhds (hball hz)))
  have hSD : ∀ z ∈ closedBall (0 : E) R,
      ‖fderiv ℂ S z - ContinuousLinearMap.id ℂ E‖ ≤ 1 / 4 := by
    intro z hz
    change ‖fderiv ℂ (Ai ∘ T) z - ContinuousLinearMap.id ℂ E‖ ≤ 1 / 4
    rw [fderiv_comp z Ai.differentiableAt
      ((hT z (hball hz)).differentiableAt (hO.mem_nhds (hball hz))), Ai.fderiv, ← hleft,
      ← ContinuousLinearMap.comp_sub]
    exact hD z hz
  have happ : ApproximatesLinearOn S (ContinuousLinearMap.id ℂ E)
      (closedBall (0 : E) R) (1 / 4 : ℝ≥0) := by
    intro u hu v hv
    exact (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le'
      hSd hSD hv hu
  let idRight : (ContinuousLinearMap.id ℂ E).NonlinearRightInverse :=
    { toFun := id
      nnnorm := 1
      bound' := by intro y; simp
      right_inv' := by intro y; rfl }
  have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse idRight hR.le Set.Subset.rfl
  have hS0 : S 0 = 0 := by simp [S, hT0]
  have hwball : Ai w ∈ closedBall (S 0) (((idRight.nnnorm : ℝ)⁻¹ - (1 / 4 : ℝ≥0)) * R) := by
    norm_num [hS0, idRight, mem_closedBall, dist_zero_right]
    linarith
  obtain ⟨z, hz, hSz⟩ := hsurj hwball
  have hAi : Function.Injective Ai := by
    have hi : Function.LeftInverse A Ai := by
      intro y
      have hh := congrArg (fun L : E →L[ℂ] E => L y) hright
      exact hh
    exact hi.injective
  exact ⟨z, hz, hAi hSz⟩

end Yau.NodeProofs.U02ContractionAux
