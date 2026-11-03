import Yau.Proofs.Y03Grid

/-! The actual trace and grid time gaps give a uniform positive conjugation scale. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem dimension_pos_of_clockRateInput {X : KahlerManifold n} {o : Pt X} {h : Flow X}
    {time : ℝ → ℝ} {s₀ a₀ b₀ : ℝ} (hrate : ClockRateInput o h time s₀ a₀ b₀) : 0 < n := by
  obtain ⟨c, hc, hbound⟩ := hrate.2.1
  have hb := hbound s₀ le_rfl
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  simp [clockSpeed, scalarCurvature, traceWith, Matrix.trace] at hb
  linarith

theorem trace_time_scale {μ : Fin n → ℝ} {q B ch T Δ S j : ℝ}
    (hn : 0 < n) (hB : 0 < B) (hT : 0 < T) (_hj : 0 < j)
    (hupper : ∀ i, μ i ≤ B * q) (htrace : (∑ i, μ i) = Δ / T)
    (hstep : ch * Real.sqrt S ≤ Δ) :
    (ch / ((n : ℝ) * B)) * Real.sqrt S / j ^ 2 ≤ (q / j ^ 2) * T := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : (∑ i, μ i) ≤ (n : ℝ) * B * q := by
    calc
      _ ≤ ∑ _i : Fin n, B * q := Finset.sum_le_sum fun i _ => hupper i
      _ = _ := by simp [mul_assoc]
  rw [htrace] at hsum
  have hΔ : Δ ≤ (n : ℝ) * B * q * T := (div_le_iff₀ hT).1 hsum
  have hden : 0 < (n : ℝ) * B := mul_pos hnR hB
  have hbase : ch * Real.sqrt S / ((n : ℝ) * B) ≤ q * T := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hdivide := div_le_div_of_nonneg_right hbase (sq_nonneg j)
  convert hdivide using 1 <;> ring

end Yau.Blueprint.Alignment.Y03Proof
