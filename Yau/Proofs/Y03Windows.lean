import Yau.Proofs.Y03Grid

/-! Scalar consequences of regularity in the actual flagged macro windows. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem regular_not_flag {Q : ℕ → ℝ} {N : ℕ} {M : ℝ} {j : ℕ}
    (hj : Regular Q N M j) : ¬ Flag Q N M j := by
  intro hf
  apply hj
  exact ⟨j, hf, Nat.sub_le _ _, by omega⟩

theorem regular_growth_bound {Q : ℕ → ℝ} {N : ℕ} {M : ℝ} {j : ℕ}
    (hj : Regular Q N M j) (hNj : N ≤ j)
    (hleft : 0 < Q (j - N)) (hright : 0 < Q (j + 1)) :
    Q (j + 1) ≤ Real.exp M * Q (j - N) := by
  have hlog : Real.log (Q (j + 1)) ≤ M + Real.log (Q (j - N)) := by
    have hnot := regular_not_flag hj
    have hle : Real.log (Q (j + 1)) - Real.log (Q (j - N)) ≤ M := by
      by_contra hn
      exact hnot ⟨hNj, lt_of_not_ge hn⟩
    linarith
  have hexp := Real.exp_le_exp.2 hlog
  simpa only [Real.exp_log hright, Real.exp_add, Real.exp_log hleft] using hexp

theorem regular_local_comparability {Q : ℕ → ℝ} {N L : ℕ} {M : ℝ} {j : ℕ}
    (hj : Regular Q N M j) (hNj : N ≤ j) (hLj : L ≤ j - N)
    (hmono : MonotoneOn Q (Set.Ici L)) (hpos : ∀ r, L ≤ r → 0 < Q r) :
    Real.exp (-M) * Q j ≤ Q (j - N) ∧ Q (j + 1) ≤ Real.exp M * Q j := by
  have hgrowth := regular_growth_bound hj hNj (hpos _ hLj) (hpos _ (by omega))
  have hLj' : L ≤ j := hLj.trans (Nat.sub_le j N)
  have hLj1 : L ≤ j + 1 := by omega
  have hQj : Q (j - N) ≤ Q j := hmono hLj hLj' (Nat.sub_le j N)
  have hQnext : Q j ≤ Q (j + 1) := hmono hLj' hLj1 (by omega)
  constructor
  · have hmul := mul_le_mul_of_nonneg_left (hQnext.trans hgrowth) (Real.exp_pos (-M)).le
    have hcancel : Real.exp (-M) * (Real.exp M * Q (j - N)) = Q (j - N) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    exact hmul.trans_eq hcancel
  · exact hgrowth.trans (mul_le_mul_of_nonneg_left hQj (Real.exp_pos M).le)

theorem sampledSpeed_monotone_late {n : ℕ} {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {time : ℝ → ℝ} {s₀ a₀ b₀ hm : ℝ}
    (hrate : ClockRateInput o h time s₀ a₀ b₀) (hhm : 0 < hm)
    {J : ℕ} (hJ : s₀ ≤ macroClock hm J) :
    MonotoneOn (sampledSpeed o h time hm) (Set.Ici J) := by
  intro i hi j hj hij
  exact hrate.1 (hJ.trans ((macroClock_strictMono hm hhm).monotone hi))
    (hJ.trans ((macroClock_strictMono hm hhm).monotone hj))
    ((macroClock_strictMono hm hhm).monotone hij)

theorem sampledSpeed_lower_late {n : ℕ} {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {time : ℝ → ℝ} {s₀ a₀ b₀ hm : ℝ}
    (hrate : ClockRateInput o h time s₀ a₀ b₀) (hhm : 0 < hm)
    {J : ℕ} (hJ : s₀ ≤ macroClock hm J) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, J ≤ j → c ≤ sampledSpeed o h time hm j := by
  obtain ⟨c, hc, hbound⟩ := hrate.2.1
  exact ⟨c, hc, fun j hj => hbound _ (hJ.trans ((macroClock_strictMono hm hhm).monotone hj))⟩

end Yau.Blueprint.Alignment.Y03Proof
