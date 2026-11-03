import Yau.Proofs.Y01GridModels

/-! The literal grid tends through macro indices to infinity, and regular
steps have a uniformly bounded increment of the square-root clock. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open scoped Topology

variable {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}

theorem gridClock_one_le (hhm : 0 < hm) (k : ℕ) : 1 ≤ gridClock Q N M hm j₀ k := by
  apply le_trans _ (gridClock_mem_Ico Q N M hm hhm j₀ k).1
  apply Real.one_le_exp_iff.mpr
  exact mul_nonneg hhm.le (Nat.cast_nonneg _)

theorem macroAt_tendsto (hhm : 0 < hm) (hgrid : GridLayout Q N M hm j₀) :
    Tendsto (macroAt Q N M hm j₀) atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [(tendsto_atTop.mp hgrid.2.2.1) (macroClock hm (j + 1))] with k hk
  by_contra hn
  have hindex : macroAt Q N M hm j₀ k + 1 ≤ j + 1 := by omega
  have hclock := (macroClock_strictMono hm hhm).monotone hindex
  have hupper := (gridClock_mem_Ico Q N M hm hhm j₀ k).2
  linarith

theorem sqrt_increment_le {s t Ch : ℝ} (hs : 1 ≤ s) (hst : s ≤ t)
    (hstep : t - s ≤ Ch * Real.sqrt s) : Real.sqrt t ≤ Real.sqrt s + Ch / 2 := by
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := hs0.trans hst
  have hx : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by linarith)
  have hxy : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hst
  have hsquare := Real.sq_sqrt hs0
  have htsquare := Real.sq_sqrt ht0
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxy)]

theorem regular_sqrt_increment (hhm : 0 < hm) (hgrid : GridLayout Q N M hm j₀) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      Real.sqrt (gridClock Q N M hm j₀ (k + 1)) ≤ Real.sqrt (gridClock Q N M hm j₀ k) + L := by
  obtain ⟨ch, Ch, hch, hCh, hsteps⟩ := hgrid.2.2.2.2.2
  refine ⟨Ch / 2, by positivity, ?_⟩
  intro k hk
  exact sqrt_increment_le (gridClock_one_le hhm k)
    (hgrid.2.1.monotone (Nat.le_succ k)) ((hsteps k).2.2 hk)

theorem macro_decay_real_eventually {a c C : ℝ} (ha : 0 < a) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      (1 + x) ^ C * Real.exp (-c * (Real.exp (a * x) / x ^ 2)) ≤ Real.exp (-x) := by
  have hlim : Tendsto (fun x : ℝ => Real.exp (a * x) / x ^ 3) atTop atTop := by
    simpa only [Real.rpow_natCast] using tendsto_exp_mul_div_rpow_atTop (3 : ℕ) a ha
  filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_atTop.1 hlim) ((C + 1) / c)] with x hx hpay
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hclock : (C + 1) * x ≤ c * (Real.exp (a * x) / x ^ 2) := by
    have hp := (div_le_div_iff₀ hc (pow_pos hxpos 3)).mp hpay
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hxpos)).mpr
    nlinarith
  have hlog : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
    linarith
  rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + x), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hlog hC]

theorem macro_decay_nat_eventually {c C : ℝ} (hhm : 0 < hm) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop,
      (1 + (j : ℝ)) ^ C * Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2) ≤
        Real.exp (-(j : ℝ)) := by
  have h : ∀ᶠ j : ℕ in atTop,
      (1 + (j : ℝ)) ^ C * Real.exp (-c * (Real.exp (hm / 2 * j) / (j : ℝ) ^ 2)) ≤ Real.exp (-(j : ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually (macro_decay_real_eventually (a := hm / 2) (by linarith) hc hC)
  filter_upwards [h] with j hj
  have heq : hm / 2 * (j : ℝ) = hm * (j : ℝ) / 2 := by ring
  rw [heq] at hj
  have hlhs : -c * Real.exp (hm * (j : ℝ) / 2) / (j : ℝ) ^ 2 =
      -c * (Real.exp (hm * (j : ℝ) / 2) / (j : ℝ) ^ 2) := by ring
  rw [← hlhs] at hj
  simpa only [macroClock, ← Real.exp_half] using hj

theorem grid_decay_tendsto_zero {c C : ℝ} (hhm : 0 < hm) (hc : 0 < c) (hC : 0 ≤ C)
    (hgrid : GridLayout Q N M hm j₀) :
    Tendsto (fun k => (1 + (macroAt Q N M hm j₀ k : ℝ)) ^ C *
      Real.exp (-c * Real.sqrt (gridClock Q N M hm j₀ k) / (macroAt Q N M hm j₀ k : ℝ) ^ 2))
      atTop (𝓝 0) := by
  let j := macroAt Q N M hm j₀
  have hj : Tendsto j atTop atTop := macroAt_tendsto hhm hgrid
  have hexp : Tendsto (fun k => Real.exp (-(j k : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.comp hj))
  apply squeeze_zero' (Eventually.of_forall (fun k => by positivity)) _ hexp
  filter_upwards [hj.eventually (macro_decay_nat_eventually hhm hc hC)] with k hk
  apply le_trans _ hk
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonpos_left
    (Real.sqrt_le_sqrt (gridClock_mem_Ico Q N M hm hhm j₀ k).1) (by linarith)

end Yau.Proofs.Y06Aux
