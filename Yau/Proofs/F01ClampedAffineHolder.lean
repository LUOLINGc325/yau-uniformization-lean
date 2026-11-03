import Yau.Proofs.F01ClampedHolder

/-! Fixed spatial sup and Lipschitz budgets give the actual parabolic
Holder bound for A(x)+t_+ B(x) on the original initial-surface cylinder.
The numerical budget is chosen before A and B. -/
noncomputable section
open Set Metric
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem linear_le_bounded_holder_power {d R β : ℝ}
    (hd : 0 ≤ d) (hR : 0 < R) (hdR : d ≤ R) (hβ : β ≤ 1) :
    d ≤ R ^ (1 - β) * d ^ β := by
  by_cases hzero : d = 0
  · rw [hzero]
    positivity
  have hpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hzero)
  calc
    d = d ^ (1 - β) * d ^ β := by rw [← Real.rpow_add hpos]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hd hdR (sub_nonneg.mpr hβ)) (Real.rpow_nonneg hd _)

theorem exists_clamped_affine_holder_budget {M β : ℝ} (hM : 0 ≤ M) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ A B : Space n → V,
      (∀ x ∈ ball (0 : Space n) 1, ‖A x‖ ≤ M ∧ ‖B x‖ ≤ M) →
      (∀ x ∈ ball (0 : Space n) 1, ∀ y ∈ ball (0 : Space n) 1,
        ‖A x - A y‖ ≤ M * ‖x - y‖ ∧ ‖B x - B y‖ ≤ M * ‖x - y‖) →
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => A p.1 + max p.2 0 • B p.1) K := by
  let Ka := 2 * M * (2 : ℝ) ^ (1 - β)
  let Kb := M * (2 : ℝ) ^ (1 - β / 2)
  let K := 1 + 2 * M + Ka + Kb
  have hKa : 0 ≤ Ka := by dsimp only [Ka]; positivity
  have hKb : 0 ≤ Kb := by dsimp only [Kb]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro A B hsup hlip
  have htime (p : Point n) (hp : p ∈ cylinder (ball (0 : Space n) 1) (-1) 1) :
      0 ≤ max p.2 0 ∧ max p.2 0 ≤ 1 := ⟨le_max_right _ _, max_le hp.2.2 zero_le_one⟩
  refine ⟨hK.le, ?_, ?_⟩
  · intro p hp
    have ha := (hsup p.1 hp.1).1
    have hb := (hsup p.1 hp.1).2
    have hs : ‖max p.2 0 • B p.1‖ ≤ M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (htime p hp).1]
      exact (mul_le_mul_of_nonneg_left hb (htime p hp).1).trans
        (by nlinarith [(htime p hp).2])
    exact (norm_add_le _ _).trans (by dsimp only [K]; linarith)
  · intro p hp q hq
    let d := ‖p.1 - q.1‖
    let e := |p.2 - q.2|
    have hd : 0 ≤ d := norm_nonneg _
    have he : 0 ≤ e := abs_nonneg _
    have hd2 : d ≤ 2 := by
      have hp1 : ‖p.1‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hp.1
      have hq1 : ‖q.1‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hq.1
      exact (norm_sub_le _ _).trans (by linarith)
    have he2 : e ≤ 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hp.2.1, hp.2.2, hq.2.1, hq.2.2]
    have hprod : ‖max p.2 0 • (B p.1 - B q.1)‖ ≤ M * d := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (htime p hp).1]
      exact (mul_le_mul_of_nonneg_left (hlip p.1 hp.1 q.1 hq.1).2 (htime p hp).1).trans
        (by nlinarith [(htime p hp).2, mul_nonneg hM hd])
    have hdiff : ‖(max p.2 0 - max q.2 0) • B q.1‖ ≤ M * e := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hsup q.1 hq.1).2 (abs_nonneg _)).trans
        (by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right (abs_time_clamp_sub_le p.2 q.2) hM)
    have hid : A p.1 + max p.2 0 • B p.1 - (A q.1 + max q.2 0 • B q.1) =
        (A p.1 - A q.1) + max p.2 0 • (B p.1 - B q.1) +
          (max p.2 0 - max q.2 0) • B q.1 := by module
    have hlinear : ‖A p.1 + max p.2 0 • B p.1 - (A q.1 + max q.2 0 • B q.1)‖ ≤ 2 * M * d + M * e := by
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (hlip p.1 hp.1 q.1 hq.1).1 hprod)) hdiff) |>.trans_eq (by ring)
    have hdp := linear_le_bounded_holder_power hd (by norm_num : (0 : ℝ) < 2) hd2 hβ
    have hep := linear_le_bounded_holder_power he (by norm_num : (0 : ℝ) < 2) he2 (by linarith : β / 2 ≤ 1)
    have hKaK : Ka ≤ K := by dsimp only [K]; linarith
    have hKbK : Kb ≤ K := by dsimp only [K]; linarith
    calc
      _ ≤ 2 * M * d + M * e := hlinear
      _ ≤ 2 * M * ((2 : ℝ) ^ (1 - β) * d ^ β) + M * ((2 : ℝ) ^ (1 - β / 2) * e ^ (β / 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hdp (by positivity)) (mul_le_mul_of_nonneg_left hep hM)
      _ = Ka * d ^ β + Kb * e ^ (β / 2) := by dsimp only [Ka, Kb]; ring
      _ ≤ K * d ^ β + K * e ^ (β / 2) := add_le_add
        (mul_le_mul_of_nonneg_right hKaK (Real.rpow_nonneg hd _))
        (mul_le_mul_of_nonneg_right hKbK (Real.rpow_nonneg he _))
      _ = K * holderWeight β p q := by dsimp only [d, e, holderWeight]; ring

end Yau.NodeProofs.F01Aux
