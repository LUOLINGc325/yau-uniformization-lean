import Yau.Proofs.C03RadialBarrier

/-! One fixed smooth local weight becomes a genuine global smooth psh
weight while retaining its actual seed/pole germs and uniform inner bound. -/

noncomputable section
open Filter Set Metric
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_global_psh_weight (R s M : ℝ) (hR : 0 < R)
    (hs : 0 ≤ s) (hsR : s < R) (hM : 0 ≤ M)
    (f : ComplexVector n → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfp : ∀ z ∈ ball (0 : ComplexVector n) R, (leviC f z).PosSemidef)
    (hupper : ∀ z ∈ ball (0 : ComplexVector n) R, f z ≤ M)
    (T : Set (ComplexVector n)) (hT : T ⊆ closedBall (0 : ComplexVector n) s)
    (hfn : ∀ z ∈ T, 0 ≤ f z) :
    ∃ F : ComplexVector n → ℝ, ContDiff ℝ ∞ F ∧
      (∀ z, (leviC F z).PosSemidef) ∧
      (∀ z ∈ ball (0 : ComplexVector n) R, F z ≤ M + 3) ∧
      ∀ z ∈ T, F =ᶠ[𝓝 z] f := by
  obtain ⟨L, hL, hsep⟩ := exists_radialBarrier_separation (n := n) R s M hs hsR hM
  let b := radialBarrier (n := n) R M L
  have hb : ContDiff ℝ ∞ b := radialBarrier_contDiff R M L
  have hupperClosed (z : ComplexVector n) (hz : ‖z‖ ≤ R) : f z ≤ M := by
    have H : closure (ball (0 : ComplexVector n) R) ⊆ {w | f w ≤ M} :=
      closure_minimal (fun w hw => hupper w hw) (isClosed_le hf.continuous continuous_const)
    apply H
    rw [closure_ball (0 : ComplexVector n) hR.ne']
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hboundary (z : ComplexVector n) (hz : ‖z‖ = R) : f z + 4 * (1 / 4 : ℝ) ≤ b z := by
    rw [show b z = M + 2 from radialBarrier_boundary R M L z hz]
    linarith [hupperClosed z hz.le]
  let F := gluedMaximum R (1 / 4) f b
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  refine ⟨F, gluedMaximum_contDiff R (1 / 4) hδ f b hf hb hboundary, ?_, ?_, ?_⟩
  · intro z
    exact gluedMaximum_leviC_posSemidef R (1 / 4) hδ f b hf hb hboundary
      (fun w hw => hfp w (by simpa only [mem_ball, dist_zero_right] using hw))
      (radialBarrier_leviC_posSemidef R M L hL.le) z
  · intro z hz
    have hz' : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
    change gluedMaximum R (1 / 4) f b z ≤ M + 3
    rw [gluedMaximum, if_pos hz']
    apply regularizedMaxCoords_le (fun _ : Bool => (1 / 4 : ℝ))
      (fun i => if i then b z else f z) (fun _ => hδ)
    intro i
    cases i
    · change f z + 1 / 4 ≤ M + 3
      linarith [hupper z hz]
    · change b z + 1 / 4 ≤ M + 3
      have H := radialBarrier_le R M L hR.le hL.le z hz'.le
      change b z ≤ M + 2 at H
      linarith
  · intro z hz
    have hz' : ‖z‖ ≤ s := by simpa only [mem_closedBall, dist_zero_right] using hT hz
    apply gluedMaximum_eq_original_germ R (1 / 4) hδ f b hf.continuous hb.continuous z
      (hz'.trans_lt hsR)
    have H := hsep z hz'
    change b z ≤ -2 at H
    linarith [hfn z hz]

end Yau.Proofs.C03Aux
