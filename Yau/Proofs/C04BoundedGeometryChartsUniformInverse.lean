import Yau.Proofs.C04BoundedGeometryChartsInverseDerivative
import Yau.Proofs.C04InverseJets

/-! The quantitative inverse is the same map at every derivative order. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Nontrivial E]
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem exists_uniform_inverse_of_coordinate_function (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) :
    ∃ P : ℕ → ℝ, (∀ m, 0 < P m) ∧
      ∀ F : E → E, ContDiff ℝ ∞ F → F 0 = 0 →
        (∀ x ∈ Metric.ball (0 : E) (1 / 2 : ℝ),
          ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) →
        (∀ m x, x ∈ Metric.ball (0 : E) (1 / 4 : ℝ) → ‖iteratedFDeriv ℝ m F x‖ ≤ B m) →
        ∃ e : OpenPartialHomeomorph E E,
          (e : E → E) = F ∧ e.source = Metric.ball 0 (1 / 2 : ℝ) ∧
          Metric.closedBall (0 : E) (3 / 16 : ℝ) ⊆ e.target ∧
          e.symm 0 = 0 ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
          (∀ w ∈ e.target, ‖e.symm w‖ ≤ (4 / 3 : ℝ) * ‖w‖) ∧
          ∀ m w, w ∈ Metric.ball (0 : E) (1 / 8 : ℝ) → ‖iteratedFDeriv ℝ m e.symm w‖ ≤ P m := by
  obtain ⟨P, hP, hbound⟩ := C04Aux.same_inverse_jet_bounds (E := E) B hB
  refine ⟨P, hP, ?_⟩
  intro F hF hF0 hclose hjet
  obtain ⟨e, he, hs, ht, h0, hsm, hnorm⟩ := inverse_on_fixed_ball F hF hF0 hclose
  have h8 : Metric.ball (0 : E) (1 / 8 : ℝ) ⊆ e.target := by
    intro w hw
    exact ht (Metric.closedBall_subset_closedBall (by norm_num : (1 / 8 : ℝ) ≤ 3 / 16)
      (Metric.ball_subset_closedBall hw))
  have himage (w : E) (hw : w ∈ Metric.ball (0 : E) (1 / 8 : ℝ)) :
      e.symm w ∈ Metric.ball (0 : E) (1 / 4 : ℝ) := by
    have hh := hnorm w (h8 hw)
    have hn : ‖w‖ < 1 / 8 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcomp (w : E) (hw : w ∈ Metric.ball (0 : E) (1 / 8 : ℝ)) : F (e.symm w) = w := by
    rw [← he]
    exact e.right_inv (h8 hw)
  have hinv (w : E) (hw : w ∈ Metric.ball (0 : E) (1 / 8 : ℝ)) :
      (fderiv ℝ F (e.symm w)).IsInvertible ∧ ‖(fderiv ℝ F (e.symm w)).inverse‖ ≤ (4 / 3 : ℝ) := by
    have hx : e.symm w ∈ Metric.ball (0 : E) (1 / 2 : ℝ) :=
      Metric.ball_subset_ball (by norm_num) (himage w hw)
    have hD := hclose (e.symm w) hx
    have hi := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one _
      (hD.trans_lt (by norm_num))
    refine ⟨hi, ?_⟩
    obtain ⟨L, hL⟩ := hi
    rw [← hL, ContinuousLinearMap.inverse_equiv]
    apply inverse_norm_le_of_close_id
    rw [hL]
    exact hD
  refine ⟨e, he, hs, ht, h0, hsm, hnorm, ?_⟩
  exact hbound F e.symm hF (hsm.mono h8) himage hcomp hjet hinv

end Yau.Proofs.C04ChartsAux
