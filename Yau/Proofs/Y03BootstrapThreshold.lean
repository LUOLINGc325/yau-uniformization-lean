import Yau.Proofs.Y03BootstrapDecay

/-! The closed backward induction uses one late threshold, independent of every finite horizon. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem uniform_bootstrap_threshold {hm c C eps B : ℝ} (hhm : 0 < hm) (hc : 0 < c)
    (hC : 0 ≤ C) (heps : 0 < eps) (hB : 0 < B) :
    ∃ J : ℕ, ∀ j, J ≤ j → 1 ≤ j ∧
      (1 + (j : ℝ)) ^ C * Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2) ≤ 1 / 2 ∧
      (1 + (j : ℝ)) ^ C * Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2) ≤
        eps / (64 * B * (j : ℝ) ^ 2) := by
  have hdecay := bootstrap_decay_nat_eventually hhm hc (by linarith : 0 ≤ C + 2)
  have hexp : Tendsto (fun j : ℕ => Real.exp (-(j : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have htol : 0 < min (1 / 2 : ℝ) (eps / (64 * B)) := by positivity
  have hsmall : ∀ᶠ j : ℕ in atTop, Real.exp (-(j : ℝ)) ≤ min (1 / 2 : ℝ) (eps / (64 * B)) :=
    (tendsto_order.1 hexp).2 _ htol |>.mono fun _ h => h.le
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hdecay.and (hsmall.and (eventually_ge_atTop (1 : ℕ))))
  refine ⟨J, ?_⟩
  intro j hj
  obtain ⟨hd, hs, hj1⟩ := hJ j hj
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  let F := (1 + (j : ℝ)) ^ C * Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2)
  have hF : 0 ≤ F := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hfactor : (1 + (j : ℝ)) ^ (C + 2) = (1 + (j : ℝ)) ^ C * (1 + (j : ℝ)) ^ 2 := by
    rw [Real.rpow_add (by positivity), Real.rpow_two]
  rw [hfactor] at hd
  have hFd : F * (1 + (j : ℝ)) ^ 2 ≤ Real.exp (-(j : ℝ)) := by
    dsimp [F]
    nlinarith
  have hmono : F ≤ F * (1 + (j : ℝ)) ^ 2 := by nlinarith
  refine ⟨hj1, hmono.trans (hFd.trans ((min_le_left _ _).trans' hs)), ?_⟩
  have hpay : F * (j : ℝ) ^ 2 ≤ eps / (64 * B) := by
    exact (by nlinarith : F * (j : ℝ) ^ 2 ≤ F * (1 + (j : ℝ)) ^ 2).trans
      (hFd.trans (hs.trans (min_le_right _ _)))
  have hp := (le_div_iff₀ (by positivity : 0 < 64 * B)).1 hpay
  apply (le_div_iff₀ (by positivity : 0 < 64 * B * (j : ℝ) ^ 2)).2
  nlinarith

end Yau.Blueprint.Alignment.Y03Proof
