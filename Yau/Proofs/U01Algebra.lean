import Yau.Blueprint.Convergence
import Yau.Proofs.U03PolynomialAlgebra

/-! Exact finite inverse-segment identities on the original polynomial sequence. -/
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.U01Proof
open Yau Blueprint.U03Proof
variable {n m : ℕ}

theorem segment_succ_eval (Ginv : ℕ → PolyMap n) (k r : ℕ) (z : ComplexVector n) :
    (backwardSegment Ginv k (r + 1)).eval z =
      (Ginv k).eval ((backwardSegment Ginv (k + 1) r).eval z) := by
  induction r generalizing z with
  | zero => simp [backwardSegment, eval_comp, eval_id]
  | succ r ih =>
    simpa only [backwardSegment, eval_comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using ih ((Ginv (k + (r + 1))).eval z)

def approx (Ginv : ℕ → PolyMap n)
    (zeta : ℕ → ComplexVector m → ComplexVector n) (k r : ℕ)
    (z : ComplexVector m) : ComplexVector n :=
  (backwardSegment Ginv k r).eval (zeta (k + r) z)

@[simp] theorem approx_zero (Ginv : ℕ → PolyMap n)
    (zeta : ℕ → ComplexVector m → ComplexVector n) (k : ℕ) (z : ComplexVector m) :
    approx Ginv zeta k 0 z = zeta k z := by
  simp [approx, backwardSegment, eval_id]

theorem approx_succ (Ginv : ℕ → PolyMap n)
    (zeta : ℕ → ComplexVector m → ComplexVector n) (k r : ℕ) (z : ComplexVector m) :
    approx Ginv zeta k (r + 1) z = (Ginv k).eval (approx Ginv zeta (k + 1) r z) := by
  simp only [approx, segment_succ_eval]
  congr 2
  congr 1
  omega

theorem polynomial_eval_differentiable (P : PolyMap n) : Differentiable ℂ P.eval := by
  classical
  apply (differentiable_piLp 2).2
  intro i
  change Differentiable ℂ (fun z : ComplexVector n => MvPolynomial.eval (fun j => z j) (P i))
  simp_rw [MvPolynomial.eval_eq']
  apply Differentiable.fun_sum
  intro β _
  apply Differentiable.const_mul
  have hp : ∀ S : Finset (Fin n), Differentiable ℂ
      (fun z : ComplexVector n => ∏ j ∈ S, z j ^ β j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using (differentiable_const (1 : ℂ))
    | @insert a S ha ih =>
      simp only [Finset.prod_insert ha]
      exact (((PiLp.proj 2 (fun _ : Fin n => ℂ) a).differentiable).pow _).mul ih
  exact hp Finset.univ

theorem approx_differentiableOn {Ω : Set (ComplexVector m)}
    (Ginv : ℕ → PolyMap n) (zeta : ℕ → ComplexVector m → ComplexVector n)
    (hz : ∀ k, DifferentiableOn ℂ (zeta k) Ω) (k r : ℕ) :
    DifferentiableOn ℂ (approx Ginv zeta k r) Ω :=
  (polynomial_eval_differentiable _).comp_differentiableOn (hz _)

end Yau.NodeProofs.U01Proof
