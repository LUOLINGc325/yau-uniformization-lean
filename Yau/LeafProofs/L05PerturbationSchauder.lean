import Yau.LeafProofs.L05PerturbationStatement
import Yau.LeafProofs.L05PerturbationNormalization
import Yau.LeafProofs.L05PerturbationSchauderAssembly

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- Finite perturbation assembly from the complete original autonomous
endpoint. The autonomous argument is the sole remaining analytic parameter. -/
theorem variable_concave_coarse_schauder_of_autonomous
    (hAuto : ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
      ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
        ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
          ConcaveOn ℝ univ F → F 0 = 0 → ∀ u : Point n → ℝ,
          ContinuousOn u (unitClosed n) → (∀ p ∈ unitClosed n, |u p| ≤ 1) →
          viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
          SchauderBound eta (backward (1/2)) u C) :
    VariableConcaveCoarseSchauderGap := by
  intro n hn alpha beta ell L M fB uB ha ha1 hb hb1 hell hL hM hfb hub
  obtain ⟨eta,rstar,E,J,he,heAB,hrstar,_,hE,hJ,hCenters⟩ :=
    perturb_centered_actual_estimates_of_autonomous hAuto n hn
      alpha beta ell L M fB uB ha ha1 hb hb1 hell hL hM hfb hub
  let C := 1+J+8*E*4^(2+eta)+2*J*(4/rstar)^eta
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨eta,C,he,heAB,hC,?_⟩
  intro Phi f u hJoint hEll hConc hCoeff hAnchor hf hu hSup hPDE
  have hAt := hCenters Phi f u hJoint hEll hConc hCoeff hAnchor hf hu hSup hPDE
  have he1 : eta ≤ 1 := ((heAB.trans_le (min_le_left _ _)).trans ha1).le
  exact perturb_schauder_of_centered_estimates hu he.le he1 hrstar hE.le hJ.le
    (fun z hz => (hAt z hz).1) (fun z hz => (hAt z hz).2)

end Yau.LeafProofs.L05Aux
