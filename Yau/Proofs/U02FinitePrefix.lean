import Yau.Proofs.U02PolynomialBounds

/-! Fixed-prefix identities and uniform convergence after composing with
that very polynomial prefix. -/

open scoped Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau

theorem backwardComp_eval_split {n : ℕ} (Ginv : ℕ → PolyMap n) (a m : ℕ)
    (z : ComplexVector n) :
    (backwardComp Ginv (a + m)).eval z =
      (backwardComp Ginv a).eval ((backwardSegment Ginv a m).eval z) := by
  induction m generalizing z with
  | zero => simp only [Nat.add_zero, backwardSegment, polynomial_eval_id]
  | succ m ih =>
    rw [Nat.add_succ, backwardComp, polynomial_eval_comp, ih,
      backwardSegment, polynomial_eval_comp]

theorem forward_backward_eval_cancel {n : ℕ} {P Q : PolyMap n}
    (h : IsPolyAutomorphism P Q) (z : ComplexVector n) : P.eval (Q.eval z) = z := by
  rw [← polynomial_eval_comp, h.1, polynomial_eval_id]

theorem polynomial_uniform_compact_limit {n : ℕ} {T : Type*} [TopologicalSpace T]
    {K : Set T} (hK : IsCompact K) {seq : ℕ → T → ComplexVector n}
    {f : T → ComplexVector n} (hf : ContinuousOn f K)
    (hlim : TendstoUniformlyOn seq f atTop K) (P : PolyMap n) :
    TendstoUniformlyOn (fun k x => P.eval (seq k x)) (fun x => P.eval (f x)) atTop K := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hf).isBounded.exists_norm_le
  let R := max C 0 + 1
  have hfR : ∀ x ∈ K, f x ∈ closedBall (0 : ComplexVector n) R := by
    intro x hx
    have hh := hC _ ⟨x, hx, rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using
      (hh.trans (by dsimp [R]; linarith [le_max_left C 0]))
  have hsR : ∀ᶠ k in atTop, ∀ x ∈ K, seq k x ∈ closedBall (0 : ComplexVector n) R := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) 1 (by norm_num)] with k hk
    intro x hx
    have hn : ‖seq k x - f x‖ < 1 := by
      have hh : dist (seq k x) (f x) < 1 := by simpa only [dist_comm] using hk x hx
      simpa only [dist_eq_norm] using hh
    have hh := hC _ ⟨x, hx, rfl⟩
    have htri := norm_le_norm_sub_add (seq k x) (f x)
    rw [mem_closedBall, dist_zero_right]
    dsimp [R]
    linarith [le_max_left C 0]
  have huc := (isCompact_closedBall (0 : ComplexVector n) R).uniformContinuousOn_of_continuous
    (polynomial_contDiff P).continuous.continuousOn
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hsR hfR huc hlim

end Yau.NodeProofs.U02Proof
