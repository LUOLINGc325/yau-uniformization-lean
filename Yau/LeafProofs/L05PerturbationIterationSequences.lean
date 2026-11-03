import Yau.LeafProofs.L05PerturbationIterationStep

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic
section FixedIteration
variable {n : ℕ} {ell L alpha beta rho eta delta K : ℝ}
variable {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ}
variable (hr : 0 < rho) (hr1 : rho < 1) (he : 0 < eta) (heAB : eta < min alpha beta)
    (ha : 0 < alpha) (hb : 0 < beta) (hd : 0 < delta) (hK : 0 < K)
    (hStep : ∀ (Phi' : Sym n → Point n → ℝ) (f' v : Point n → ℝ),
      perturbSmallData ell L delta Phi' f' v →
      ∃ (d : ℝ) (e : Space n →L[ℝ] ℝ) (B : Sym n) (s : ℝ),
        |d| ≤ K ∧ ‖e‖ ≤ K ∧ ‖B‖ ≤ K ∧ |s| ≤ K ∧ s=Phi' B (0,0) ∧
        ∀ p∈perturbClosed (0 : Space n) rho 0, |v p-perturbPolynomial d e B s p| ≤ rho^(2+eta))
    (hData : perturbHolderData ell L alpha beta (delta/(4*(1+K/(1-rho^eta)))) (delta/4) Phi f u)

def perturbIterationNext (k : ℕ)
    (P : {P : perturbIterationTuple n // perturbIterationInvariant rho eta K Phi f u k P}) :
    {P' : perturbIterationTuple n // perturbIterationInvariant rho eta K Phi f u (k+1) P'} :=
  ⟨Classical.choose (perturb_iteration_step_exists hr hr1 he heAB ha hb hd hK hStep hData k P.val P.property),
    (Classical.choose_spec (perturb_iteration_step_exists hr hr1 he heAB ha hb hd hK hStep hData k P.val P.property)).1⟩

theorem perturb_iteration_next_spec (k : ℕ)
    (P : {P : perturbIterationTuple n // perturbIterationInvariant rho eta K Phi f u k P}) :
    |(perturbIterationNext hr hr1 he heAB ha hb hd hK hStep hData k P).val.1-P.val.1| ≤ K*(rho^k : ℝ)^(2+eta) ∧
      ‖(perturbIterationNext hr hr1 he heAB ha hb hd hK hStep hData k P).val.2.1-P.val.2.1‖ ≤ K*(rho^k : ℝ)^(1+eta) ∧
      ‖(perturbIterationNext hr hr1 he heAB ha hb hd hK hStep hData k P).val.2.2.1-P.val.2.2.1‖ ≤ K*(rho^k : ℝ)^eta ∧
      |(perturbIterationNext hr hr1 he heAB ha hb hd hK hStep hData k P).val.2.2.2-P.val.2.2.2| ≤ K*(rho^k : ℝ)^eta :=
  (Classical.choose_spec (perturb_iteration_step_exists hr hr1 he heAB ha hb hd hK hStep hData k P.val P.property)).2

def perturbIterationRun : (k : ℕ) →
    {P : perturbIterationTuple n // perturbIterationInvariant rho eta K Phi f u k P}
  | 0 => ⟨(0,0,0,0),perturb_iteration_zero_invariant hData⟩
  | k+1 => perturbIterationNext hr hr1 he heAB ha hb hd hK hStep hData k
      (perturbIterationRun k)

include hr hr1 he heAB ha hb hd hK hStep hData in
theorem perturb_sequences_from_step :
    ∃ (c : ℕ → ℝ) (b : ℕ → Space n →L[ℝ] ℝ) (A : ℕ → Sym n) (q : ℕ → ℝ),
      c 0=0 ∧ b 0=0 ∧ A 0=0 ∧ q 0=0 ∧
      (∀ k, q k=Phi (A k) (0,0)+f (0,0)) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ p∈perturbClosed (0 : Space n) (rho^k) 0,
        |u p-perturbPolynomial (c k) (b k) (A k) (q k) p| ≤ (rho^k : ℝ)^(2+eta)) ∧
      (∀ k, |c (k+1)-c k| ≤ K*(rho^k : ℝ)^(2+eta)) ∧
      (∀ k, ‖b (k+1)-b k‖ ≤ K*(rho^k : ℝ)^(1+eta)) ∧
      (∀ k, ‖A (k+1)-A k‖ ≤ K*(rho^k : ℝ)^eta) ∧
      (∀ k, |q (k+1)-q k| ≤ K*(rho^k : ℝ)^eta) ∧
      ∀ k, ‖A k‖ ≤ K/(1-rho^eta) := by
  let S := perturbIterationRun hr hr1 he heAB ha hb hd hK hStep hData
  let c := fun k => (S k).val.1
  let b := fun k => (S k).val.2.1
  let A := fun k => (S k).val.2.2.1
  let q := fun k => (S k).val.2.2.2
  have hInc (k : ℕ) := perturb_iteration_next_spec hr hr1 he heAB ha hb hd hK hStep hData k (S k)
  refine ⟨c,b,A,q,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k
    exact (S k).property.2.1
  · intro k hk
    exact (S k).property.2.2.1 hk
  · intro k
    exact (hInc k).1
  · intro k
    exact (hInc k).2.1
  · intro k
    exact (hInc k).2.2.1
  · intro k
    exact (hInc k).2.2.2
  · intro k
    exact (S k).property.2.2.2.trans (perturb_geometric_partial_budget (Real.rpow_nonneg hr.le _)
      (Real.rpow_lt_one hr.le hr1 he) hK.le k)

end FixedIteration
end Yau.LeafProofs.L05Aux
