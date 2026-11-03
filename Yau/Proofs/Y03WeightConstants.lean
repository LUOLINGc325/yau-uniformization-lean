import Yau.Proofs.Y03WeightEstimates
import Yau.Proofs.Y03Windows

/-! Choose all weight constants before one uniform late threshold and every grid start. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem regular_rate_bounds_from_windows {Q : ℕ → ℝ} {N L j : ℕ} {M b₀ b : ℝ}
    (hreg : Regular Q N M j) (hNj : N ≤ j) (hLj : L ≤ j - N)
    (hmono : MonotoneOn Q (Set.Ici L)) (hpos : ∀ r, L ≤ r → 0 < Q r)
    (hb₀ : 0 ≤ b₀) (hb : 0 < b) (hbleft : b ≤ Real.exp (-M) * b₀)
    (hbright : b * Real.exp M ≤ 1) {μ : ℝ}
    (hwindow : b₀ * Q (j - N) ≤ μ ∧ μ ≤ Q (j + 1)) :
    b * Q j ≤ μ ∧ μ ≤ b⁻¹ * Q j := by
  have hcomp := regular_local_comparability hreg hNj hLj hmono hpos
  have hQ : 0 ≤ Q j := (hpos j (hLj.trans (Nat.sub_le j N))).le
  constructor
  · have hcompLow : (Real.exp (-M) * b₀) * Q j ≤ b₀ * Q (j - N) := by
      nlinarith [mul_le_mul_of_nonneg_left hcomp.1 hb₀]
    exact (mul_le_mul_of_nonneg_right hbleft hQ).trans (hcompLow.trans hwindow.1)
  · have hu := hwindow.2.trans hcomp.2
    have hpay := mul_le_mul_of_nonneg_right hbright hQ
    have hmul := mul_le_mul_of_nonneg_left hu hb.le
    have hdiv : μ ≤ Q j / b := (le_div_iff₀ hb).2 (by nlinarith)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv

theorem weightEstimates_uniform_constants (Q : ℕ → ℝ) (N : ℕ) (M hm b₀ c : ℝ)
    (_hM : 0 < M) (hhm : 0 < hm) (hb₀ : 0 < b₀) (hc : 0 < c) (L : ℕ)
    (hQmono : MonotoneOn Q (Set.Ici L)) (hQlower : ∀ j, L ≤ j → c ≤ Q j) :
    ∃ scale K eps b : ℝ, 0 < scale ∧ 0 < K ∧ 0 < eps ∧
      eps < 1 / (10 * (n + 1 : ℝ)) ∧ 0 < b ∧
      ∃ J : ℕ, ∀ j₀, J ≤ j₀ → ∀ μ : ℕ → Fin n → ℝ,
        (∀ i, Monotone (fun k => μ k i)) → WindowRateBounds Q N M hm b₀ j₀ μ →
          WeightEstimates Q N M hm scale K eps b j₀ μ := by
  let b := Real.exp (-M) * min 1 b₀ / 2
  have hb : 0 < b := div_pos (mul_pos (Real.exp_pos _) (lt_min zero_lt_one hb₀)) (by norm_num)
  have hbleft : b ≤ Real.exp (-M) * b₀ := by
    have hmin : min 1 b₀ ≤ b₀ := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hmin (Real.exp_pos (-M)).le
    dsimp [b]
    nlinarith [mul_pos (Real.exp_pos (-M)) hb₀]
  have hbright : b * Real.exp M ≤ 1 := by
    have heq : b * Real.exp M = min 1 b₀ / 2 := by
      dsimp [b]
      rw [mul_div_assoc, mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [heq]
    have := min_le_left (1 : ℝ) b₀
    linarith
  let K := 4 / b
  have hK : 0 < K := div_pos (by norm_num) hb
  have hKb : 2 ≤ K * b := by dsimp [K]; rw [div_mul_cancel₀ _ hb.ne']; norm_num
  let eps := 1 / (100 * ((n : ℝ) + 1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsBound : eps < 1 / (10 * (n + 1 : ℝ)) := by
    dsimp [eps]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have heps' : eps ≤ 0.9 := by
    dsimp [eps]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hsmall : (n : ℝ) * eps ≤ 0.1 := by
    dsimp [eps]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  let scale := max 1 (4 / (b * c))
  have hscale : 0 < scale := zero_lt_one.trans_le (le_max_left _ _)
  have hscaleLower : 2 ≤ scale * b * c := by
    have h4 : 4 ≤ scale * (b * c) := (div_le_iff₀ (mul_pos hb hc)).1 (le_max_right _ _)
    nlinarith
  obtain ⟨Jsize, hJsize⟩ := exists_nat_gt (max 1 (max (2 / b) K))
  let J := max (L + N) Jsize
  have hsize (j : ℕ) (hj : J ≤ j) : 0 < (j : ℝ) ∧ 2 / b ≤ (j : ℝ) ^ 2 ∧
      K ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
    have hJnat : Jsize ≤ j := (le_max_right _ _).trans hj
    have hjR : (Jsize : ℝ) ≤ j := by exact_mod_cast hJnat
    have h1 : 1 < (j : ℝ) := (le_max_left _ _).trans_lt (hJsize.trans_le hjR)
    have hbR : 2 / b < (j : ℝ) :=
      (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt (hJsize.trans_le hjR))
    have hKR : K < (j : ℝ) :=
      (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt (hJsize.trans_le hjR))
    push_cast
    refine ⟨by linarith, by nlinarith, by nlinarith⟩
  refine ⟨scale, K, eps, b, hscale, hK, heps, hepsBound, hb, J, ?_⟩
  intro j₀ hj₀ μ hmono hwindow
  have hQpos (j : ℕ) (hj : L ≤ j) : 0 < Q j := hc.trans_le (hQlower j hj)
  apply weightEstimates_of_uniform_rate_bounds Q N M hm hhm scale K eps b c j₀ μ
    hscale hK.le heps.le hb hc hsmall heps' hKb hscaleLower hmono
  · intro j hj
    exact hQlower j (by have := (le_max_left _ _).trans (hj₀.trans hj); omega)
  · intro j hj
    have hs := hsize j (hj₀.trans hj)
    have hQj := (hQpos j (by have := (le_max_left _ _).trans (hj₀.trans hj); omega)).le
    have hbpay : 2 ≤ b * (j : ℝ) ^ 2 := by
      simpa only [mul_comm] using (div_le_iff₀ hb).1 hs.2.1
    have hpay := mul_le_mul_of_nonneg_right hbpay hQj
    unfold theta
    apply (div_le_iff₀ (sq_pos_of_pos hs.1)).2
    nlinarith
  · intro j hj
    exact (div_le_one (sq_pos_of_pos (by positivity : (0 : ℝ) < (j + 1 : ℕ)))).2
      (hsize j (hj₀.trans hj)).2.2
  · intro k i hreg
    let j := macroAt Q N M hm j₀ k
    have hj : J ≤ j := hj₀.trans (macroAt_mem Q N M hm j₀ k).1
    have hLj : L + N ≤ j := (le_max_left _ _).trans hj
    exact regular_rate_bounds_from_windows hreg (by omega) (by omega) hQmono hQpos
      hb₀.le hb hbleft hbright (hwindow k i hreg)

end Yau.Blueprint.Alignment.Y03Proof
