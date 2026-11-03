import Yau.Proofs.U01Algebra
import Yau.Proofs.U01Estimates

/-! Simultaneous control of all finite backward iterates inside the proved tubes. -/
open Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.U01Proof
open Yau Blueprint.U03Proof
variable {n m : ℕ} {Ω : Set (ComplexVector m)}
    {s : ℕ → ℝ} {G Ginv : ℕ → PolyMap n}
    {zeta : ℕ → ComplexVector m → ComplexVector n} {nu delta : ℝ} {K : ℕ}

section Finite
variable (hn : 0 < nu) (hn' : nu < 1 / 10) (hd : delta < 1 / 10)
    (hstep : ∀ k, 1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k)
    (hlarge : ∀ k, K ≤ k → 1 ≤ s k)
    (hsmall : ∀ k, K ≤ k → Real.exp (-nu * s k) < 1 / 2)
    (hauto : ∀ k, IsPolyAutomorphism (G k) (Ginv k))
    (hzeta : ∀ k, K ≤ k → ∀ z ∈ Ω,
      ‖zeta k z‖ ≤ Real.exp (-2 * nu * s k) ∧
      ‖zeta (k + 1) z - (G k).eval (zeta k z)‖ ≤ Real.exp (-10 * s k))
    (hlip : ∀ k, K ≤ k → ∀ u v : ComplexVector n,
      ‖u‖ < Real.exp (-nu * s (k + 1)) → ‖v‖ < Real.exp (-nu * s (k + 1)) →
      ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤
        Real.exp (s (k + 1) - s k) * ‖u - v‖)

include hn hn' hd hstep hlarge hsmall hauto hzeta hlip

theorem finite_error (r k : ℕ) (hk : K ≤ k) (z : ComplexVector m) (hz : z ∈ Ω) :
    ‖approx Ginv zeta k r z - zeta k z‖ ≤ Real.exp (-7 * s k) := by
  induction r generalizing k with
  | zero => simp only [approx_zero, sub_self, norm_zero]; positivity
  | succ r ih =>
    have hk1 : K ≤ k + 1 := by omega
    have hnext := ih (k + 1) hk1
    have hb := tube_budget (by linarith [hlarge k hk])
      (by linarith [hlarge (k + 1) hk1]) hn hn' hd (hstep k).2 (hsmall (k + 1) hk1)
    have hytube : ‖approx Ginv zeta (k + 1) r z‖ < Real.exp (-nu * s (k + 1)) := by
      calc
        _ ≤ ‖approx Ginv zeta (k + 1) r z - zeta (k + 1) z‖ + ‖zeta (k + 1) z‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ Real.exp (-7 * s (k + 1)) + Real.exp (-2 * nu * s (k + 1)) :=
          add_le_add hnext (hzeta (k + 1) hk1 z hz).1
        _ < _ := by linarith [hb.1]
    have hgtube : ‖(G k).eval (zeta k z)‖ < Real.exp (-nu * s (k + 1)) := by
      calc
        _ ≤ ‖(G k).eval (zeta k z) - zeta (k + 1) z‖ + ‖zeta (k + 1) z‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ Real.exp (-10 * s k) + Real.exp (-2 * nu * s (k + 1)) := by
          rw [norm_sub_rev]
          exact add_le_add (hzeta k hk z hz).2 (hzeta (k + 1) hk1 z hz).1
        _ < _ := by linarith [hb.2]
    have h := hlip k hk _ _ hytube hgtube
    rw [inverse_eval_forward (hauto k)] at h
    rw [approx_succ]
    refine h.trans ((mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le).trans
      (inverse_budget (hlarge k hk) (hstep k).1 (hstep k).2 hd))
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hnext (hzeta k hk z hz).2)

theorem finite_tube (r k : ℕ) (hk : K ≤ k) (z : ComplexVector m) (hz : z ∈ Ω) :
    ‖approx Ginv zeta (k + 1) r z‖ < Real.exp (-nu * s (k + 1)) ∧
    ‖(G k).eval (zeta k z)‖ < Real.exp (-nu * s (k + 1)) := by
  have hk1 : K ≤ k + 1 := by omega
  have hb := tube_budget (by linarith [hlarge k hk])
    (by linarith [hlarge (k + 1) hk1]) hn hn' hd (hstep k).2 (hsmall (k + 1) hk1)
  constructor
  · calc
      _ ≤ ‖approx Ginv zeta (k + 1) r z - zeta (k + 1) z‖ + ‖zeta (k + 1) z‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ Real.exp (-7 * s (k + 1)) + Real.exp (-2 * nu * s (k + 1)) :=
        add_le_add (finite_error hn hn' hd hstep hlarge hsmall hauto hzeta hlip r (k + 1) hk1 z hz)
          (hzeta (k + 1) hk1 z hz).1
      _ < _ := by linarith [hb.1]
  · calc
      _ ≤ ‖(G k).eval (zeta k z) - zeta (k + 1) z‖ + ‖zeta (k + 1) z‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ Real.exp (-10 * s k) + Real.exp (-2 * nu * s (k + 1)) := by
        rw [norm_sub_rev]
        exact add_le_add (hzeta k hk z hz).2 (hzeta (k + 1) hk1 z hz).1
      _ < _ := by linarith [hb.2]

theorem terminal_difference (r R k : ℕ) (hk : K ≤ k)
    (z : ComplexVector m) (hz : z ∈ Ω) :
    ‖approx Ginv zeta k r z - approx Ginv zeta k (r + R) z‖ ≤
      Real.exp (-s k - 6 * s (k + r)) := by
  induction r generalizing k with
  | zero =>
    simp only [Nat.zero_add, Nat.add_zero, approx_zero]
    rw [norm_sub_rev]
    have he : -s k - 6 * s k = -7 * s k := by ring
    rw [he]
    exact finite_error hn hn' hd hstep hlarge hsmall hauto hzeta hlip R k hk z hz
  | succ r ih =>
    have hk1 : K ≤ k + 1 := by omega
    have h1 := (finite_tube hn hn' hd hstep hlarge hsmall hauto hzeta hlip r k hk z hz).1
    have h2 := (finite_tube hn hn' hd hstep hlarge hsmall hauto hzeta hlip (r + R) k hk z hz).1
    have h := hlip k hk _ _ h1 h2
    have hid : r + 1 + R = (r + R) + 1 := by omega
    rw [hid, approx_succ, approx_succ]
    refine h.trans ((mul_le_mul_of_nonneg_left (ih (k + 1) hk1) (Real.exp_pos _).le).trans_eq ?_)
    rw [← Real.exp_add]
    congr 1
    have hind : k + 1 + r = k + (r + 1) := by omega
    rw [hind]
    ring

end Finite
end Yau.NodeProofs.U01Proof
