import Yau.LeafProofs.L05PerturbationPolynomialTails
import Yau.LeafProofs.L05PerturbationActualJets
import Yau.LeafProofs.L05PerturbationTaylorBasic

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbIterationCoefficientSum (rho sigma K : ℝ) : ℝ := K/(1-rho^sigma)

def perturbIterationRemainderBudget (rho eta K : ℝ) : ℝ :=
  (1+perturbIterationCoefficientSum rho (2+eta) K+perturbIterationCoefficientSum rho (1+eta) K+
    (1/2 : ℝ)*perturbIterationCoefficientSum rho eta K+perturbIterationCoefficientSum rho eta K)*rho^(-(2+eta))

theorem perturb_iteration_coefficient_sum_pos {rho sigma K : ℝ} (hr : 0 < rho)
    (hr1 : rho < 1) (hs : 0 < sigma) (hK : 0 < K) : 0 < perturbIterationCoefficientSum rho sigma K :=
  div_pos hK (sub_pos.mpr (Real.rpow_lt_one hr.le hr1 hs))

theorem perturb_iteration_remainder_budget_pos {rho eta K : ℝ} (hr : 0 < rho)
    (hr1 : rho < 1) (he : 0 < eta) (hK : 0 < K) : 0 < perturbIterationRemainderBudget rho eta K := by
  have hSc := perturb_iteration_coefficient_sum_pos hr hr1 (show 0 < 2+eta by linarith) hK
  have hSb := perturb_iteration_coefficient_sum_pos hr hr1 (show 0 < 1+eta by linarith) hK
  have hSA := perturb_iteration_coefficient_sum_pos hr hr1 he hK
  dsimp only [perturbIterationRemainderBudget]
  positivity

theorem perturb_iteration_origin_actual_estimates {n : ℕ} {rho eta K : ℝ}
    (hr : 0 < rho) (hr1 : rho < 1) (he : 0 < eta) (hK : 0 < K)
    {u : Point n → ℝ} (hu : C2 (backward 1) u)
    (c q : ℕ → ℝ) (b : ℕ → Space n →L[ℝ] ℝ) (A : ℕ → Sym n)
    (hc0 : c 0=0) (hb0 : b 0=0) (hA0 : A 0=0) (hq0 : q 0=0)
    (hc : ∀ k : ℕ, |c (k+1)-c k| ≤ K*(rho^k : ℝ)^(2+eta))
    (hb : ∀ k : ℕ, ‖b (k+1)-b k‖ ≤ K*(rho^k : ℝ)^(1+eta))
    (hA : ∀ k : ℕ, ‖A (k+1)-A k‖ ≤ K*(rho^k : ℝ)^eta)
    (hq : ∀ k : ℕ, |q (k+1)-q k| ≤ K*(rho^k : ℝ)^eta)
    (hError : ∀ k : ℕ, 1 ≤ k → ∀ p∈perturbClosed (0 : Space n) (rho^k) 0,
      |u p-perturbPolynomial (c k) (b k) (A k) (q k) p| ≤ (rho^k : ℝ)^(2+eta)) :
    |u (0,0)| ≤ perturbIterationCoefficientSum rho (2+eta) K ∧
      ‖spatialD u (0,0)‖ ≤ perturbIterationCoefficientSum rho (1+eta) K ∧
      ‖hessian u (0,0)‖ ≤ perturbIterationCoefficientSum rho eta K ∧
      ‖spatialDD u (0,0)‖ ≤ perturbIterationCoefficientSum rho eta K ∧
      |timeD (backward 1) u (0,0)| ≤ perturbIterationCoefficientSum rho eta K ∧
      ∀ r : ℝ, 0 < r → r ≤ rho → ∀ p∈perturbClosed (0 : Space n) r 0,
        |u p-perturbTaylor (backward 1) u (0,0) p| ≤ perturbIterationRemainderBudget rho eta K*r^(2+eta) := by
  let Sc := perturbIterationCoefficientSum rho (2+eta) K
  let Sb := perturbIterationCoefficientSum rho (1+eta) K
  let SA := perturbIterationCoefficientSum rho eta K
  have hSc : 0 < Sc := perturb_iteration_coefficient_sum_pos hr hr1 (by linarith) hK
  have hSb : 0 < Sb := perturb_iteration_coefficient_sum_pos hr hr1 (by linarith) hK
  have hSA : 0 < SA := perturb_iteration_coefficient_sum_pos hr hr1 he hK
  have hJ : 0 ≤ 1+Sc+Sb+(1/2 : ℝ)*SA+SA := by positivity
  obtain ⟨ci,qi,bi,Ai,_,_,_,_,hCN,hBN,hAN,hQN,hCT,hBT,hAT,hQT⟩ :=
    perturb_polynomial_coefficient_limits hr hr1 he c q b A hc0 hb0 hA0 hq0 hc hb hA hq
  have hCont := perturb_polynomial_continuous_remainder hr hr1 he hJ u c q b A ci qi bi Ai hCT hBT hAT hQT hError
  have hE : 0 ≤ perturbIterationRemainderBudget rho eta K := (perturb_iteration_remainder_budget_pos hr hr1 he hK).le
  have hApprox : ∀ r : ℝ, 0 < r → r ≤ rho → ∀ p∈perturbClosed (0 : Space n) r 0,
      |u p-perturbPolynomial ci bi Ai qi p| ≤ perturbIterationRemainderBudget rho eta K*r^(2+eta) := hCont
  obtain ⟨hci,hbi,hAi,hqi⟩ := perturb_identify_polynomial hu he hE hr hr1 bi Ai hApprox
  have hHessian : ‖hessian u (0,0)‖ ≤ SA := by rw [← hAi]; exact hAN
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hDD : ‖spatialDD u (0,0)‖ ≤ SA := by
    rw [perturb_spatialDD_eq_bilinear hu hOrigin]
    exact (perturbBilinear_norm_le _).trans hHessian
  refine ⟨?_,?_,hHessian,hDD,?_,?_⟩
  · rw [← hci]
    exact hCN
  · rw [← hbi]
    exact hBN
  · rw [← hqi]
    exact hQN
  · intro r hr' hrR p hp
    change |u p-perturbTaylor (backward 1) u (0 : Point n) p| ≤ _
    rw [perturb_taylor_origin_polynomial hu hOrigin]
    change |u p-perturbPolynomial (u (0,0)) (spatialD u (0,0)) (hessian u (0,0))
      (timeD (backward 1) u (0,0)) p| ≤ _
    simpa only [hci,hbi,hAi,hqi] using hApprox r hr' hrR p hp

end Yau.LeafProofs.L05Aux
