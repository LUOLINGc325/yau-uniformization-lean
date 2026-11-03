import Yau.LeafProofs.L05PerturbationIterationSequences

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_polynomial_iteration_of_autonomous
    (hAuto : ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
      ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
        ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
          ConcaveOn ℝ univ F → F 0=0 → ∀ u : Point n → ℝ,
          ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p| ≤ 1) →
          viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
          SchauderBound eta (backward (1/2)) u C)
    (n : ℕ) (hn : 0< n) (ell L alpha beta : ℝ)
    (hell : 0< ell) (hL : ell≤ L)
    (ha : 0< alpha) (ha1 : alpha< 1) (hb : 0< beta) (hb1 : beta< 1) :
    ∃ eta rho K mu0 af0 : ℝ,
      0< eta ∧ eta< min alpha beta ∧ 0< rho ∧ rho≤ 1/16 ∧
      0< K ∧ 0< mu0 ∧ 0< af0 ∧
      ∀ (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ),
        perturbHolderData ell L alpha beta mu0 af0 Phi f u →
        ∃ (c : ℕ → ℝ) (b : ℕ → Space n →L[ℝ] ℝ)
          (A : ℕ → Sym n) (q : ℕ → ℝ),
          c 0=0 ∧ b 0=0 ∧ A 0=0 ∧ q 0=0 ∧
          (∀ k, q k=Phi (A k) (0,0)+f (0,0)) ∧
          (∀ k : ℕ, 1≤ k →
            ∀ p ∈ perturbClosed (0 : Space n) (rho^k) 0,
              |u p-perturbPolynomial (c k) (b k) (A k) (q k) p|
                ≤ (rho^k : ℝ)^(2+eta)) ∧
          (∀ k, |c (k+1)-c k|≤ K*(rho^k : ℝ)^(2+eta)) ∧
          (∀ k, ‖b (k+1)-b k‖≤ K*(rho^k : ℝ)^(1+eta)) ∧
          (∀ k, ‖A (k+1)-A k‖≤ K*(rho^k : ℝ)^eta) ∧
          (∀ k, |q (k+1)-q k|≤ K*(rho^k : ℝ)^eta) ∧
          ∀ k, ‖A k‖≤ K/(1-rho^eta) := by
  obtain ⟨eta,rho,delta,K,he,heAB,hr,hrb,hd,_,hK,hStep⟩ :=
    perturb_one_step_of_autonomous hAuto n hn ell L alpha beta hell hL ha ha1 hb hb1
  have hr1 : rho < 1 := lt_of_le_of_lt hrb (by norm_num)
  let Astar := K/(1-rho^eta)
  let mu0 := delta/(4*(1+Astar))
  let af0 := delta/4
  have hNumbers : 0 < Astar ∧ 0 < mu0 ∧ 0 < af0 ∧ 4*(mu0*(1+Astar))=delta ∧ 4*af0=delta :=
    perturb_iteration_smallness_budgets hr hr1 he hK hd
  refine ⟨eta,rho,K,mu0,af0,he,heAB,hr,hrb,hK,hNumbers.2.1,hNumbers.2.2.1,?_⟩
  intro Phi f u hData
  exact perturb_sequences_from_step hr hr1 he heAB ha hb hd hK hStep hData

end Yau.LeafProofs.L05Aux
