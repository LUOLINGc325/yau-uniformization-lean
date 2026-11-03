import Yau.Proofs.F04SeeleyProducts

/-! Exact finite Lagrange moment identities for the explicit reflection weights. -/

noncomputable section

namespace Yau.F04Proof.Seeley

open Polynomial

theorem dyadic_strictMono : StrictMono dyadic := by
  apply strictMono_nat_of_lt_succ
  intro k
  change (2 : ℝ) ^ k < (2 : ℝ) ^ (k + 1)
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]

def finiteWeight (N k : ℕ) : ℝ :=
  if k ≤ N then ∏ j ∈ (Finset.range (N + 1)).erase k,
    (1 + dyadic j) / (dyadic j - dyadic k) else 0

theorem finiteWeight_eq_eval_basis (N k : ℕ) (hk : k ≤ N) :
    finiteWeight N k =
      (Lagrange.basis (Finset.range (N + 1)) (fun j => -dyadic j) k).eval 1 := by
  rw [finiteWeight, ite_eq_left hk, Lagrange.basis, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  rw [show -dyadic k - -dyadic j = dyadic j - dyadic k by ring]
  rw [show (1 : ℝ) - -dyadic j = 1 + dyadic j by ring]
  exact div_eq_mul_inv _ _ |>.trans (mul_comm _ _)

theorem finiteWeight_eq_zero_of_lt (N k : ℕ) (hNk : N < k) : finiteWeight N k = 0 := by
  exact ite_eq_right (Nat.not_le.mpr hNk)

theorem finiteWeight_moment (N m : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Finset.range (N + 1), finiteWeight N k * (-dyadic k) ^ m) = 1 := by
  have hnodes : Set.InjOn (fun j => -dyadic j) (Finset.range (N + 1)) := by
    intro i _ j _ hij
    exact dyadic_strictMono.injective (neg_injective hij)
  have hdegree : (Polynomial.X ^ m : ℝ[X]).degree <
      (Finset.range (N + 1)).card := by
    rw [Polynomial.degree_X_pow, Finset.card_range]
    exact_mod_cast Nat.lt_succ_of_le hm
  have heq := Lagrange.eq_interpolate (s := Finset.range (N + 1))
    (v := fun j => -dyadic j) hnodes hdegree
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) heq
  rw [Lagrange.interpolate_apply] at heval
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C] at heval
  calc
    _ = ∑ k ∈ Finset.range (N + 1), (-dyadic k) ^ m *
        (Lagrange.basis (Finset.range (N + 1)) (fun j => -dyadic j) k).eval 1 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [finiteWeight_eq_eval_basis N k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      ring
    _ = 1 := heval.symm

end Yau.F04Proof.Seeley
