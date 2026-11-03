import Yau.LeafProofs.L05PerturbationFrozenLocalJets

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- The sole internal analytic parameter is exactly the original autonomous
endpoint. It is discharged by that endpoint when its independent owner lands it. -/
theorem perturb_frozen_core_jets_of_autonomous
    (hAuto : ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
      ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
        ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
          ConcaveOn ℝ univ F → F 0=0 → ∀ u : Point n → ℝ,
          ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p| ≤ 1) →
          viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
          SchauderBound eta (backward (1/2)) u C)
    (n : ℕ) (hn : 0 < n) (ell L : ℝ) (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ Kh : ℝ, 0 < Kh ∧ ∀ (F : Sym n → ℝ) (h : Point n → ℝ),
      Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0) →
      (∀ p∈perturbClosed (0 : Space n) (1/2) 0, |h p| ≤ 1) →
      viscositySolution (perturbOpen (0 : Space n) (1/2) 0) (fun H _ => F H) (fun _ => 0) h →
      ∀ tau : ℝ, 0 < tau → tau ≤ 1/8 →
        C2 (perturbCore tau) h ∧
        (∀ p∈perturbCore tau, ‖hessian h p‖ ≤ Kh*tau^(-2 : ℝ)) ∧
        ∀ p∈perturbCore tau, timeD (perturbCore tau) h p=F (hessian h p) := by
  obtain ⟨eta,C,_,_,hC,hRegular⟩ := hAuto n hn ell L hell hL
  exact perturb_frozen_core_jets_from_witness hC hRegular

end Yau.LeafProofs.L05Aux
