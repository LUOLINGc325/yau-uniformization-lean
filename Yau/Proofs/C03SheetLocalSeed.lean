import Yau.Proofs.C03SheetSeed
import Yau.Proofs.C03SheetPole

/-! A qualitative source neighborhood retains the literal n+1 pole and
the holomorphic seed. Its radius is used only for the pole jet conclusion. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux Yau.NodeProofs.P03Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem exists_sheet_seed_pole_neighborhood (O : Set (ComplexVector n)) (hO : IsOpen O)
    (h0 : (0 : ComplexVector n) ∈ O) (σ θ : ComplexVector n → ComplexVector n)
    (hθ : ContDiffOn ℂ ∞ θ O) (w0 : ComplexVector n) (hθ0 : θ 0 = w0)
    (hσ0 : σ w0 = 0) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (δs δp : ℝ) (hδs : 0 < δs) (hδp : 0 < δp) (hδps : δp ≤ δs)
    (η : Covector n) :
    ∃ R : ℝ, 0 < R ∧ ball (0 : ComplexVector n) R ⊆ O ∧
      ContDiffOn ℝ 1 (fun z => θ z - w0) (ball 0 R) ∧
      (∀ z ∈ ball (0 : ComplexVector n) R, z ≠ 0 → θ z - w0 ≠ 0) ∧
      DifferentiableOn ℂ (sheetSeed O θ δs hδs η w0) (ball 0 R) ∧
      ∀ j z, z ∈ ball (0 : ComplexVector n) R →
        sheetPole O θ δp hδp (n + 1) w0 j z =
          ((n + 1 : ℕ) : ℝ) * Real.log (‖θ z - w0‖ ^ 2 + poleEpsilon j) -
            ((n + 1 : ℕ) : ℝ) * Real.log (1 + δp ^ 2) := by
  have hc : ContinuousOn θ O := hθ.continuousOn
  have hU : IsOpen (O ∩ θ ⁻¹' ball w0 (δp / 2)) :=
    hc.isOpen_inter_preimage hO isOpen_ball
  have h0U : (0 : ComplexVector n) ∈ O ∩ θ ⁻¹' ball w0 (δp / 2) := by
    exact ⟨h0, by rw [mem_preimage, hθ0]; exact mem_ball_self (by positivity)⟩
  obtain ⟨R, hR, hRU⟩ := isOpen_iff.mp hU 0 h0U
  have hRO : ball (0 : ComplexVector n) R ⊆ O := fun z hz => (hRU hz).1
  have hpoint (z : ComplexVector n) (hz : z ∈ ball (0 : ComplexVector n) R) :
      ‖θ z - w0‖ < δp / 2 := by
    simpa only [mem_preimage, mem_ball, dist_eq_norm] using (hRU hz).2
  have heq : Set.EqOn (sheetSeed O θ δs hδs η w0) (fun z => η (θ z - w0)) (ball 0 R) := by
    intro z hz
    classical
    change (if z ∈ O then _ else _) = _
    rw [if_pos (hRO hz)]
    apply targetSeed_eq_on_inner
    rw [mem_closedBall, dist_zero_right]
    exact (hpoint z hz).le.trans (by linarith)
  have hlinear : ContDiffOn ℂ ∞ (fun z => η (θ z - w0)) (ball 0 R) :=
    η.contDiff.comp_contDiffOn ((hθ.mono hRO).sub contDiffOn_const)
  refine ⟨R, hR, hRO, ((hθ.mono hRO).sub contDiffOn_const).restrict_scalars ℝ |>.of_le (by simp),
    ?_, hlinear.differentiableOn (by simp) |>.congr heq, ?_⟩
  · intro z hz hn he
    have he' : θ z = w0 := sub_eq_zero.mp he
    have H := hστ z (hRO hz)
    rw [he', hσ0] at H
    exact hn H.symm
  · intro j z hz
    rw [sheetPole_eq_on_inner O θ δp hδp (n + 1) w0 j z (hRO hz)
      (by simpa only [mem_closedBall, dist_eq_norm] using (hpoint z hz).le)]
    ring

end Yau.Proofs.C03Aux
