import Yau.Proofs.U02FinitePrefix

/-! Exact finite-prefix and reindexing identities for the original models. -/

open scoped Topology
open Filter

namespace Yau.NodeProofs.U02Proof

open Yau

theorem backwardSegment_shift {n : ℕ} (Ginv : ℕ → PolyMap n) (N a m : ℕ) :
    backwardSegment (fun k => Ginv (k + N)) a m = backwardSegment Ginv (a + N) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [backwardSegment, ih, Nat.add_right_comm a m N]

theorem backwardComp_tail_eval {n : ℕ} (Ginv : ℕ → PolyMap n) (N a l : ℕ)
    (hal : a ≤ l) (z : ComplexVector n) :
    (backwardComp Ginv (l + N)).eval z =
      (backwardComp Ginv (a + N)).eval
        ((backwardSegment (fun k => Ginv (k + N)) a (l - a)).eval z) := by
  rw [backwardSegment_shift, ← backwardComp_eval_split]
  rw [show l + N = (a + N) + (l - a) by omega]

theorem forward_cancel_backward_tail {n : ℕ} (G Ginv : ℕ → PolyMap n) (a l : ℕ)
    (hal : a ≤ l)
    (hauto : IsPolyAutomorphism (forwardComp G a) (backwardComp Ginv a))
    (z : ComplexVector n) :
    (forwardComp G a).eval ((backwardComp Ginv l).eval z) =
      (backwardSegment Ginv a (l - a)).eval z := by
  have hl : l = a + (l - a) := by omega
  rw [hl, backwardComp_eval_split, forward_backward_eval_cancel hauto]
  congr 2
  omega

theorem tendstoUniformlyOn_nat_add_iff {n : ℕ} {T : Type*} {seq : ℕ → T → ComplexVector n}
    {psi : T → ComplexVector n} {K : Set T} (N : ℕ) :
    TendstoUniformlyOn (fun k => seq (k + N)) psi atTop K ↔
      TendstoUniformlyOn seq psi atTop K := by
  constructor
  · intro h u hu
    obtain ⟨M, hM⟩ := eventually_atTop.1 (h u hu)
    refine eventually_atTop.2 ⟨M + N, ?_⟩
    intro k hk
    have hh := hM (k - N) (by omega)
    simpa only [Nat.sub_add_cancel (show N ≤ k by omega)] using hh
  · intro h u hu
    obtain ⟨M, hM⟩ := eventually_atTop.1 (h u hu)
    exact eventually_atTop.2 ⟨M, fun k hk => hM (k + N) (by omega)⟩

end Yau.NodeProofs.U02Proof
