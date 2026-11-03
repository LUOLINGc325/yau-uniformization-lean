import Yau.Proofs.Y04FiniteCharging
import Yau.Proofs.Y03Windows

/-! Good sampled endpoints and exclusion of an all-bad late tail. -/

noncomputable section

open Filter

namespace Yau.Blueprint.Alignment.Y04Proof

open Y03Proof

theorem macroClock_bracket {hm x : ℝ} (hhm : 0 < hm) (hx : 1 ≤ x) :
    ∃ j : ℕ, macroClock hm j ≤ x ∧ x < macroClock hm (j+1) := by
  have hex : ∃ j : ℕ, x < macroClock hm (j+1) := by
    obtain ⟨m, hmc⟩ := ((tendsto_atTop.1 (macroClock_tendsto hm hhm)) (x+1)).exists
    exact ⟨m, by
      have := (macroClock_strictMono hm hhm).monotone (show m ≤ m+1 by omega)
      linarith⟩
  let j := Nat.find hex
  refine ⟨j, ?_, Nat.find_spec hex⟩
  by_cases hj : j = 0
  · simpa [hj, macroClock] using hx
  · by_contra hn
    have hprev : x < macroClock hm ((j-1)+1) := by
      simpa [Nat.sub_add_cancel (show 1 ≤ j by omega)] using lt_of_not_ge hn
    have hmin : j ≤ j-1 := Nat.find_min' hex hprev
    omega

theorem sampled_good_endpoints
    (q : ℝ → ℝ) (s₀ hm : ℝ) (jBound : ℕ)
    (hhm : 0 < hm) (hdom : s₀ ≤ macroClock hm jBound)
    (hmono : MonotoneOn q (Set.Ici s₀))
    (hsmall : ∀ S : ℝ, ∃ x : ℝ,
      max S s₀ ≤ x ∧ q x ≤ 3*x) :
    ∀ J, ∃ j, max J jBound ≤ j ∧
      q (macroClock hm j) ≤ 3*Real.exp hm*macroClock hm j := by
  intro J
  let a := max J jBound
  obtain ⟨x, hx, hqx⟩ := hsmall (macroClock hm a)
  have hax : macroClock hm a ≤ x := (le_max_left _ _).trans hx
  have hxdom : s₀ ≤ x := (le_max_right _ _).trans hx
  have h1 : 1 ≤ x := by
    have h := (macroClock_strictMono hm hhm).monotone (show 0 ≤ a by omega)
    have hzero : macroClock hm 0 = 1 := by simp [macroClock]
    rw [hzero] at h
    exact h.trans hax
  obtain ⟨j, hjlo, hjhi⟩ := macroClock_bracket hhm h1
  have haj : a ≤ j := by
    by_contra hn
    have hja : j+1 ≤ a := by omega
    have := (macroClock_strictMono hm hhm).monotone hja
    linarith
  refine ⟨j, haj, ?_⟩
  have hjdom : s₀ ≤ macroClock hm j := hdom.trans
    ((macroClock_strictMono hm hhm).monotone (by dsimp [a] at haj; omega))
  calc
    q (macroClock hm j) ≤ q x := hmono hjdom hxdom hjlo
    _ ≤ 3*x := hqx
    _ ≤ 3*Real.exp hm*macroClock hm j := by
      rw [macroClock_succ hm j] at hjhi
      linarith

theorem regular_endpoints_unbounded
    {Q : ℕ → ℝ} {jBound N : ℕ} {M hm : ℝ}
    (hM : 0 < M) (hmono : MonotoneOn Q (Set.Ici jBound))
    (hpos : ∀ j, jBound ≤ j → 0 < Q j)
    (hgap : hm < M/(3*(2*N+1:ℝ)))
    (hgood : ∀ J, ∃ j, max J jBound ≤ j ∧
      Q j ≤ 3*Real.exp hm*macroClock hm j) :
    ∀ J, ∃ j, max J jBound ≤ j ∧ Regular Q N M j := by
  classical
  intro J
  by_contra hn
  let a := max J jBound
  let W := 2*N+1
  let α := M/(3*(2*N+1:ℝ))
  have hbad : ∀ r, a ≤ r → Bad Q N M r := by
    intro r hr
    by_contra h
    exact hn ⟨r, hr, h⟩
  have hapos : 0 < Q a := hpos a (le_max_right _ _)
  have hden : 0 < α-hm := by dsimp [α]; linarith
  obtain ⟨R, hR⟩ := exists_nat_gt
    ((Real.log 3 + hm - Real.log (Q a) + α * (a+2*W:ℕ)) / (α-hm))
  obtain ⟨j, hj, hQg⟩ := hgood (max R (a+2*W))
  have haj : a ≤ j := by omega
  have hlen : a+2*W ≤ j := by omega
  have hlog := bad_interior_log_growth hM hmono hpos (le_max_right J jBound) haj
    (fun r har _ => hbad r har)
  have hcast : ((j-a-2*W:ℕ):ℝ) = (j:ℝ) - (a+2*W:ℕ) := by
    rw [Nat.sub_sub, Nat.cast_sub hlen]
  have hlogupper : Real.log (Q j / Q a) ≤
      Real.log 3 + hm + hm*j - Real.log (Q a) := by
    rw [Real.log_div (ne_of_gt (hpos j (by omega))) (ne_of_gt hapos)]
    have h := Real.log_le_log (hpos j (by omega)) hQg
    rw [Real.log_mul (by positivity : (3*Real.exp hm:ℝ) ≠ 0)
      (ne_of_gt (macroClock_pos hm j)),
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (ne_of_gt (Real.exp_pos hm)),
      Real.log_exp, macroClock, Real.log_exp] at h
    linarith
  change α * ((j-a-2*W:ℕ):ℝ) ≤ _ at hlog
  rw [hcast] at hlog
  have hR' : Real.log 3 + hm - Real.log (Q a) + α * (a+2*W:ℕ) <
      (R:ℝ) * (α-hm) := (div_lt_iff₀ hden).mp hR
  have hRj : (R:ℝ) ≤ j := by exact_mod_cast (show R ≤ j by omega)
  nlinarith

end Yau.Blueprint.Alignment.Y04Proof
