import Yau.Proofs.Y04ClockSubsequence
import Yau.Proofs.Y04Costs

/-! The complete frozen charging predicate on the original positive clock tail. -/

noncomputable section

open Filter

namespace Yau.Blueprint.Alignment.Y04Proof

open Yau Y03Proof

theorem badCharging_of_tail
    {Q : ℕ → ℝ} {jBound N Dstar : ℕ} {M hm b₀ : ℝ}
    (hD : 1 ≤ Dstar) (hM : 0 < M) (hb₀ : 0 < b₀)
    (hmono : MonotoneOn Q (Set.Ici jBound))
    (hpos : ∀ j, jBound ≤ j → 0 < Q j)
    (hpay : Real.log (Dstar:ℝ) +
      max 0 (Real.log (2/b₀))/(2*N+1:ℝ) ≤ M/(3*(2*N+1:ℝ)))
    (hgap : hm < M/(3*(2*N+1:ℝ)))
    (hgood : ∀ J, ∃ j, max J jBound ≤ j ∧
      Q j ≤ 3*Real.exp hm*macroClock hm j) :
    BadCharging Q jBound N Dstar M hm b₀ := by
  have hreg := regular_endpoints_unbounded hM hmono hpos hgap hgood
  refine ⟨hmono, hpos, ?_, ?_, ?_, hreg, hgood⟩
  · intro u v hu hc
    have hg := full_bad_log_growth hM hmono hpos hu hc
    refine ⟨by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hg, ?_⟩
    apply full_reset_cost hD (by omega : 0 < 2*N+1) (fullBadComponent_length hc)
      hb₀ (hpos u hu) (hpos (v-N) (by have := fullBadComponent_length hc; omega))
    · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hpay
    · exact hg
  · intro u j hu huj hleft hbad
    have hg := bad_prefix_log_growth hM hmono hpos hu huj hleft hbad
    refine ⟨by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hg, ?_⟩
    apply prefix_cost hD (hpos u hu) (hmono hu (hu.trans huj) huj) (α := M/(3*(2*N+1:ℝ)))
    · have hnonneg : 0 ≤ max 0 (Real.log (2/b₀))/(2*N+1:ℝ) := by positivity
      linarith
    · exact hg
  · rintro ⟨u, hleft, hbad⟩
    obtain ⟨j, hj, hjreg⟩ := hreg u
    exact hjreg (hbad j ((le_max_left _ _).trans hj))

theorem exists_badCharging_bound
    {n : ℕ} {X : KahlerManifold n} {o : Pt X} {h : Flow X}
    {time : ℝ → ℝ} {s₀ a₀ b₀ hm M : ℝ} {N Dstar : ℕ}
    (hrate : ClockRateInput o h time s₀ a₀ b₀)
    (hhm : 0 < hm) (hN : 1 ≤ N) (hD : 1 ≤ Dstar)
    (hM : 0 < M) (hb₀ : 0 < b₀)
    (hpay : Real.log (Dstar:ℝ) +
      max 0 (Real.log (2/b₀))/(2*N+1:ℝ) ≤ M/(3*(2*N+1:ℝ)))
    (hgap : hm < M/(3*(2*N+1:ℝ))) :
    ∃ jBound : ℕ, N < jBound ∧
      s₀ ≤ macroClock hm (jBound-N) ∧
      BadCharging (sampledSpeed o h time hm) jBound N Dstar M hm b₀ := by
  obtain ⟨L, hL⟩ := ((tendsto_atTop.1 (macroClock_tendsto hm hhm)) s₀).exists
  let jBound := L+N+1
  have hdom : s₀ ≤ macroClock hm jBound :=
    hL.trans ((macroClock_strictMono hm hhm).monotone (by dsimp [jBound]; omega))
  have hdom' : s₀ ≤ macroClock hm (jBound-N) :=
    hL.trans ((macroClock_strictMono hm hhm).monotone (by dsimp [jBound]; omega))
  obtain ⟨c, hc, hcQ⟩ := sampledSpeed_lower_late hrate hhm hdom
  refine ⟨jBound, by dsimp [jBound]; omega, hdom', ?_⟩
  apply badCharging_of_tail hD hM hb₀ (sampledSpeed_monotone_late hrate hhm hdom)
    (fun j hj => hc.trans_le (hcQ j hj)) hpay hgap
  exact sampled_good_endpoints _ _ _ _ hhm hdom hrate.1
    (fun S => by simpa only [show (2:ℝ)+1=3 by norm_num] using hrate.2.2.1 1 zero_lt_one S)

end Yau.Blueprint.Alignment.Y04Proof
