import Yau.LeafProofs.L05PerturbationImprovement
import Yau.LeafProofs.L05PerturbationIterationBudgets
import Yau.LeafProofs.L05PerturbationScaledClosed

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

abbrev perturbIterationTuple (n : ℕ) := ℝ × (Space n →L[ℝ] ℝ) × Sym n × ℝ

/-- A literal induction assertion on already constructed coefficients. -/
def perturbIterationInvariant {n : ℕ} (rho eta K : ℝ) (Phi : Sym n → Point n → ℝ)
    (f u : Point n → ℝ) (k : ℕ) (P : perturbIterationTuple n) : Prop :=
  (∀ p∈backward 1, |perturbIterSolution u P.1 P.2.1 P.2.2.1 P.2.2.2 (rho^k) eta p| ≤ 1) ∧
    P.2.2.2=Phi P.2.2.1 (0,0)+f (0,0) ∧
    (1 ≤ k → ∀ p∈perturbClosed (0 : Space n) (rho^k) 0,
      |u p-perturbPolynomial P.1 P.2.1 P.2.2.1 P.2.2.2 p| ≤ (rho^k : ℝ)^(2+eta)) ∧
    ‖P.2.2.1‖ ≤ K*(∑ i∈Finset.range k, (rho^eta)^i)

theorem perturb_iteration_step_exists {n : ℕ} {ell L alpha beta rho eta delta K : ℝ}
    (hr : 0 < rho) (hr1 : rho < 1) (he : 0 < eta) (heAB : eta < min alpha beta)
    (ha : 0 < alpha) (hb : 0 < beta) (hd : 0 < delta) (hK : 0 < K)
    (hStep : ∀ (Phi' : Sym n → Point n → ℝ) (f' v : Point n → ℝ),
      perturbSmallData ell L delta Phi' f' v →
      ∃ (d : ℝ) (e : Space n →L[ℝ] ℝ) (B : Sym n) (s : ℝ),
        |d| ≤ K ∧ ‖e‖ ≤ K ∧ ‖B‖ ≤ K ∧ |s| ≤ K ∧ s=Phi' B (0,0) ∧
        ∀ p∈perturbClosed (0 : Space n) rho 0, |v p-perturbPolynomial d e B s p| ≤ rho^(2+eta))
    {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ}
    (hData : perturbHolderData ell L alpha beta (delta/(4*(1+K/(1-rho^eta)))) (delta/4) Phi f u)
    (k : ℕ) (P : perturbIterationTuple n) (hInv : perturbIterationInvariant rho eta K Phi f u k P) :
    ∃ P' : perturbIterationTuple n,
      perturbIterationInvariant rho eta K Phi f u (k+1) P' ∧
      |P'.1-P.1| ≤ K*(rho^k : ℝ)^(2+eta) ∧
      ‖P'.2.1-P.2.1‖ ≤ K*(rho^k : ℝ)^(1+eta) ∧
      ‖P'.2.2.1-P.2.2.1‖ ≤ K*(rho^k : ℝ)^eta ∧
      |P'.2.2.2-P.2.2.2| ≤ K*(rho^k : ℝ)^eta := by
  let r := rho^k
  let Astar := K/(1-rho^eta)
  let mu := delta/(4*(1+Astar))
  let af := delta/4
  have hNumbers : 0 < Astar ∧ 0 < mu ∧ 0 < af ∧ 4*(mu*(1+Astar))=delta ∧ 4*af=delta :=
    perturb_iteration_smallness_budgets hr hr1 he hK hd
  have ht0 : 0 ≤ rho^eta := Real.rpow_nonneg hr.le _
  have ht1 : rho^eta < 1 := Real.rpow_lt_one hr.le hr1 he
  have hAstar : ‖P.2.2.1‖ ≤ Astar := hInv.2.2.2.trans (perturb_geometric_partial_budget ht0 ht1 hK.le k)
  have hR : 0 < r := pow_pos hr k
  have hR1 : r ≤ 1 := pow_le_one₀ hr.le hr1.le
  have hSmall := perturb_iter_small_data hR hR1 he.le ha hb (lt_min_iff.mp heAB).1.le (lt_min_iff.mp heAB).2.le
    hNumbers.2.1.le hNumbers.2.2.1.le P.2.1 P.2.2.1 hAstar hNumbers.2.2.2.1.le hNumbers.2.2.2.2.le
    hData hInv.2.1 hInv.1
  obtain ⟨d,e,B,s,hd',he',hB,hs,hCompat,hCorrect⟩ := hStep
    (perturbIterOperator Phi P.2.2.1 r eta) (perturbIterSource f r eta)
    (perturbIterSolution u P.1 P.2.1 P.2.2.1 P.2.2.2 r eta) hSmall
  let P' : perturbIterationTuple n := (P.1+r^(2+eta)*d,P.2.1+r^(1+eta) • e,
    P.2.2.1+r^eta • B,P.2.2.2+r^eta*s)
  have hError : ∀ p∈perturbClosed (0 : Space n) (rho^(k+1)) 0,
      |u p-perturbPolynomial P'.1 P'.2.1 P'.2.2.1 P'.2.2.2 p| ≤ (rho^(k+1) : ℝ)^(2+eta) := by
    simpa only [P',r,pow_succ] using perturb_iter_error_transfer hR hr u P.1 d P.2.2.2 s P.2.1 e P.2.2.1 B hCorrect
  have hSup : ∀ p∈backward 1,
      |perturbIterSolution u P'.1 P'.2.1 P'.2.2.1 P'.2.2.2 (rho^(k+1)) eta p| ≤ 1 :=
    perturb_iter_sup_of_error (pow_pos hr _) u P'.2.1 P'.2.2.1 hError
  have hQ : P'.2.2.2=Phi P'.2.2.1 (0,0)+f (0,0) :=
    perturb_iter_polynomial_compatibility hR Phi f P.2.2.1 B hInv.2.1 hCompat
  have hMat : ‖P'.2.2.1‖ ≤ K*(∑ i∈Finset.range (k+1), (rho^eta)^i) :=
    perturb_matrix_partial_update ht0 P.2.2.1 B hInv.2.2.2 hB (Real.rpow_pow_comm hr.le eta k).symm
  have hInc := perturb_iter_increment_bounds (eta := eta) (c := P.1) (q := P.2.2.2) hR P.2.1 e P.2.2.1 B hd' he' hB hs
  exact ⟨P',⟨hSup,hQ,fun _ => hError,hMat⟩,hInc⟩

theorem perturb_iteration_zero_invariant {n : ℕ} {rho eta K ell L alpha beta mu af : ℝ}
    {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ}
    (hData : perturbHolderData ell L alpha beta mu af Phi f u) :
    perturbIterationInvariant rho eta K Phi f u 0 (0,0,0,0) := by
  rcases hData.1 with ⟨_,_,_,hPhi0,hf0,_,hSup,_⟩
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [pow_zero,perturb_iter_initial_solution] using hSup
  · simp only [hPhi0,hf0,zero_add]
  · intro h
    omega
  · simp

end Yau.LeafProofs.L05Aux
