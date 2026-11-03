import Yau.Proofs.Y03FinitePrefix
import Yau.Proofs.Y03ChangeLimit
import Yau.Proofs.Y03Compactness

/-! One common coefficientwise subsequence produces the full original infinite-tail alignment. -/

open scoped Topology Matrix Matrix.Norms.Elementwise
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem alignmentRuns_of_uniform_finite (E : Frames n) (D : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (reg : ℕ → Prop) (J : ℕ → ℕ) (S : ℕ → ℝ) (C c : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hD : ∀ k, IsUnit (D k))
    (hfinite : ∀ a len : ℕ, 0 < len → (∀ r, r < len → reg (a + r)) →
      ∃ L : Changes n, L.plus (a + len - 1) = 1 ∧
        (∀ r, r < len → ChangeAt D w J S C c L (a + r)) ∧
        ∀ r, r + 1 < len → JumpAt E w L (a + r)) :
    AlignmentRuns E D w reg J S := by
  refine ⟨C, c, hC, hc, hfinite, ?_⟩
  intro a htail
  obtain ⟨finite, hfin, hbound⟩ := normalized_finite_prefix_family E D w reg J S C c hfinite a htail
  obtain ⟨A, subseq, hstrict, hlim, hcoeff⟩ := common_matrix_subsequence
    (fun H k => (finite H).plus k) (fun k => max 1 ((1 + (J k : ℝ)) ^ C)) hbound
  let L : Changes n := ⟨A, fun k => (D k)⁻¹ * A k * D k⟩
  have hplus (k : ℕ) : Tendsto (fun H => (finite (subseq H)).plus k) atTop (𝓝 (A k)) :=
    tendsto_pi_nhds.1 hlim k
  have hchange (k : ℕ) (hak : a ≤ k) : ∀ᶠ H in atTop, ChangeAt D w J S C c (finite H) k := by
    filter_upwards [eventually_ge_atTop (k - a)] with H hH
    have heq : a + (k - a) = k := Nat.add_sub_of_le hak
    simpa only [heq] using (hfin H).2.1 (k - a) hH
  have hchangeSeq (k : ℕ) (hak : a ≤ k) :
      ∀ᶠ H in atTop, ChangeAt D w J S C c (finite (subseq H)) k :=
    hstrict.tendsto_atTop.eventually (hchange k hak)
  have hminus (k : ℕ) (hak : a ≤ k) :
      Tendsto (fun H => (finite (subseq H)).minus k) atTop (𝓝 (L.minus k)) := by
    have hp : Tendsto (fun H => (D k)⁻¹ * (finite (subseq H)).plus k * D k) atTop
        (𝓝 ((D k)⁻¹ * A k * D k)) := (tendsto_const_nhds.mul (hplus k)).mul tendsto_const_nhds
    have heq : (fun H => (finite (subseq H)).minus k) =ᶠ[atTop]
        fun H => (D k)⁻¹ * (finite (subseq H)).plus k * D k :=
      (hchangeSeq k hak).mono fun H hH => hH.2.2.1
    exact hp.congr' heq.symm
  have hLchange (k : ℕ) (hak : a ≤ k) : ChangeAt D w J S C c L k := by
    have h := changeAt_limit D w J S C c k (hD k) (hplus k) (hminus k hak) (hchangeSeq k hak)
    exact h
  have hjump (k : ℕ) (hak : a ≤ k) : ∀ᶠ H in atTop, JumpAt E w (finite H) k := by
    filter_upwards [eventually_ge_atTop (k - a + 1)] with H hH
    have heq : a + (k - a) = k := Nat.add_sub_of_le hak
    simpa only [heq] using (hfin H).2.2 (k - a) (by omega)
  refine ⟨L, finite, subseq, hstrict, ?_, hfin, ?_⟩
  · intro k hak
    refine ⟨hLchange k hak, ?_⟩
    have hP : IsUnit (L.plus k) := strict_weight_isUnit _ (w k)
      (hLchange k hak).1 (hLchange k hak).2.1
    exact jump_entries_limit E w k hP (hplus k) (hminus (k + 1) (by omega))
      (hstrict.tendsto_atTop.eventually (hjump k hak))
  · intro k i l hak
    exact ⟨hcoeff k i l, tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (hminus k hak) i) l⟩

end Yau.Blueprint.Alignment.Y03Proof
