import Yau.LeafProofs.L16HalfSpaceSchauderTransport

/-! The literal native three point reflection is a projection, and does not
enlarge a spatial support ball. These statements use the actual formula. -/

open Set
open scoped Topology
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_normalSample_norm_ge {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {j : ℝ} (hj : 1 ≤ j) (x : Space n) : ‖x‖ ≤ ‖normalSample e j x‖ := by
  have hsq : ‖normalSample e j x‖ ^ 2 =
      ‖x‖ ^ 2 + (j^2-1)*(inner ℝ e x)^2 := by
    unfold normalSample
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,
      sq_abs,he,one_pow,mul_one,real_inner_comm x e]
    ring
  have hpos : 0 ≤ (j^2-1)*(inner ℝ e x)^2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  nlinarith [norm_nonneg x,norm_nonneg (normalSample e j x)]

theorem F05_reflection_idempotent {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (v : Point n → ℝ) :
    halfSpaceSecondOrderExtension e (halfSpaceSecondOrderExtension e v) =
      halfSpaceSecondOrderExtension e v := by
  funext p
  by_cases hp : 0 ≤ inner ℝ e p.1
  · simp only [halfSpaceSecondOrderExtension,ite_eq_left hp]
  · have hs (j : ℝ) (hj : 0 ≤ j) : 0 ≤ inner ℝ e (normalSample e j p.1) := by
      rw [normalSample_normal he]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) (lt_of_not_ge hp).le
    simp only [halfSpaceSecondOrderExtension,ite_eq_right hp,
      ite_eq_left (hs 1 (by norm_num)),ite_eq_left (hs 2 (by norm_num)),ite_eq_left (hs 3 (by norm_num))]

theorem F05_reflection_zero_outside {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {R : ℝ} {v : Point n → ℝ}
    (hv : ∀ p, 0 ≤ inner ℝ e p.1 → R < ‖p.1‖ → v p = 0)
    {p : Point n} (hp : R < ‖p.1‖) : halfSpaceSecondOrderExtension e v p = 0 := by
  by_cases hn : 0 ≤ inner ℝ e p.1
  · simpa only [halfSpaceSecondOrderExtension,ite_eq_left hn] using hv p hn hp
  · have hs (j : ℝ) (hj : 1 ≤ j) : v (normalSample e j p.1,p.2) = 0 := by
      apply hv
      · rw [normalSample_normal he]
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (le_trans (by norm_num) hj)) (lt_of_not_ge hn).le
      · exact hp.trans_le (F05_normalSample_norm_ge he hj p.1)
    simp only [halfSpaceSecondOrderExtension,ite_eq_right hn,hs 1 (by norm_num),
      hs 2 (by norm_num),hs 3 (by norm_num),mul_zero,sub_zero,add_zero]

theorem F05_reflection_tsupport {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {R : ℝ} {v : Point n → ℝ}
    (hv : ∀ p, 0 ≤ inner ℝ e p.1 → R < ‖p.1‖ → v p = 0) (t : ℝ) :
    tsupport (fun x => halfSpaceSecondOrderExtension e v (x,t)) ⊆ Metric.closedBall 0 R := by
  change closure (Function.support (fun x => halfSpaceSecondOrderExtension e v (x,t))) ⊆ _
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hOut
  have hR : R < ‖x‖ := by
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hOut
  exact hx (F05_reflection_zero_outside he hv hR)

end Yau.Proofs.F05Aux
