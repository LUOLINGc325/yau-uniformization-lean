import Yau.LeafProofs.L23ContractionWordNorm
import Yau.LeafProofs.L23CovariantTrace
import Yau.LeafProofs.L23CovariantPermutation

/-! A single metric trace with arbitrary free covariant slots. Its routing is
finite data; differentiation preserves the trace and adds the new free slot. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n r q : ℕ} {M : ComplexManifold n}

abbrev SingleTraceWord (r q : ℕ) := Fin r ≃ (Fin 2 ⊕ Fin q)

def singleTraceSlotIndex (q : ℕ) : (Fin 2 ⊕ Fin q) ≃ Fin (q + 2) :=
  finSumFinEquiv.trans (rankIndexEquiv (Nat.add_comm 2 q))

theorem singleTraceSlotIndex_free (j : Fin q) :
    singleTraceSlotIndex q (Sum.inr j) = j.succ.succ := by
  apply Fin.ext
  change 2 + j.val = j.val + 1 + 1
  omega

def singleTraceCons (w : SingleTraceWord r q) : SingleTraceWord (r + 1) (q + 1) where
  toFun := Fin.cases (Sum.inr 0) (fun j =>
    match w j with | .inl p => .inl p | .inr a => .inr a.succ)
  invFun := Sum.elim (fun p => (w.symm (Sum.inl p)).succ)
    (Fin.cases 0 (fun a => (w.symm (Sum.inr a)).succ))
  left_inv j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · cases hw : w j with
      | inl p =>
          simp only [Fin.cases_succ, hw, Sum.elim_inl]
          change (w.symm (Sum.inl p)).succ = j.succ
          rw [← hw, w.symm_apply_apply]
      | inr a =>
          simp only [Fin.cases_succ, hw, Sum.elim_inr]
          change (w.symm (Sum.inr a)).succ = j.succ
          rw [← hw, w.symm_apply_apply]
  right_inv s := by
    cases s with
    | inl p =>
        change (match w (w.symm (Sum.inl p)) with
          | .inl p => .inl p | .inr a => .inr a.succ) = Sum.inl p
        rw [w.apply_symm_apply]
    | inr a =>
        refine Fin.cases ?_ (fun a => ?_) a
        · rfl
        · change (match w (w.symm (Sum.inr a)) with
            | .inl p => .inl p | .inr a => .inr a.succ) = Sum.inr a.succ
          rw [w.apply_symm_apply]

def singleTraceEval (w : SingleTraceWord r q) (H : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n r) (v : Fin q → RIdx n) : ℝ :=
  ∑ a : RIdx n, ∑ b : RIdx n, H a b * A (fun j => Sum.elim ![a, b] v (w j))

theorem singleTrace_tuple (w : SingleTraceWord r q) (a b : RIdx n) (v : Fin q → RIdx n) :
    (Fin.cons a (Fin.cons b v) : Fin (q + 2) → RIdx n) ∘ (w.trans (singleTraceSlotIndex q)) =
      fun j => Sum.elim ![a, b] v (w j) := by
  funext j
  change (Fin.cons a (Fin.cons b v) : Fin (q + 2) → RIdx n)
    (singleTraceSlotIndex q (w j)) = _
  cases hw : w j with
  | inl p => fin_cases p <;> rfl
  | inr i => rw [singleTraceSlotIndex_free]; rfl

theorem singleTraceEval_eq_metricTrace (w : SingleTraceWord r q)
    (H : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) :
    singleTraceEval w H A = tensorMetricTrace H
      (fun v => A (v ∘ (w.trans (singleTraceSlotIndex q)))) := by
  funext v
  simp only [singleTraceEval, tensorMetricTrace, singleTrace_tuple]

theorem singleTraceEval_cons (w : SingleTraceWord r q)
    (H : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n (r + 1))
    (i : RIdx n) (v : Fin q → RIdx n) :
    singleTraceEval (singleTraceCons w) H A (Fin.cons i v) =
      ∑ a : RIdx n, ∑ b : RIdx n,
        H a b * A (Fin.cons i (fun j => Sum.elim ![a, b] v (w j))) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · cases hw : w j <;> simp [singleTraceCons, hw]

theorem covariantD_reindex_cons {r s : ℕ} (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (e : Fin r ≃ Fin s)
    (z : ComplexVector n) (i : RIdx n) (v : Fin s → RIdx n) :
    covariantD k c (fun w v => A w (v ∘ e)) z (Fin.cons i v) =
      covariantD k c A z (Fin.cons i (v ∘ e)) := by
  have hrs : r = s := by simpa using Fintype.card_congr e
  subst s
  exact covariantD_permute_cons k c A e z i v

set_option backward.isDefEq.respectTransparency false in
theorem covariantD_singleTraceEval (w : SingleTraceWord r q)
    (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ v, DifferentiableAt ℝ (fun u => A u v) z) (i : RIdx n) (v : Fin q → RIdx n) :
    covariantD k c (fun u => singleTraceEval w (realMetricFn k c u)⁻¹ (A u)) z (Fin.cons i v) =
      singleTraceEval (singleTraceCons w) (realMetricFn k c z)⁻¹ (covariantD k c A z)
        (Fin.cons i v) := by
  let e := w.trans (singleTraceSlotIndex q)
  have hfield : (fun u => singleTraceEval w (realMetricFn k c u)⁻¹ (A u)) =
      (fun u => tensorMetricTrace (realMetricFn k c u)⁻¹ (fun v => A u (v ∘ e))) := by
    funext u
    exact singleTraceEval_eq_metricTrace w _ _
  rw [hfield, covariantD_tensorMetricTrace k hk c _ hz (fun v => hA (v ∘ e)),
    singleTraceEval_cons]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [covariantD_reindex_cons, singleTrace_tuple]

theorem singleTraceEval_normSq_le (w : SingleTraceWord r q)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) (A : CovTensor n r) :
    covTensorNormSq G (singleTraceEval w G⁻¹ A) ≤
      (2 * n : ℕ) * covTensorNormSq G A := by
  rw [singleTraceEval_eq_metricTrace]
  apply (covTensorNormSq_metricTrace_le G hG _).trans_eq
  rw [covTensorNormSq_reindex]

end Yau.Proofs.C05Aux
