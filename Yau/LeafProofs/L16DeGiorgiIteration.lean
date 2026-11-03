import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Filter
open scoped Topology

namespace Yau.LeafProofs.L16DG

/-- The scalar induction underlying the De Giorgi small-measure iteration. -/
theorem nonlinear_iteration_geometric_bound
    {C B δ q ε : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hq : 0 < q) (hε : 0 < ε)
    (hCδ : C * δ ^ ε ≤ q) (hBq : B * q ^ ε ≤ 1)
    {Y : ℕ → ℝ} (hY : ∀ j, 0 ≤ Y j) (h0 : Y 0 ≤ δ)
    (hstep : ∀ j, Y (j + 1) ≤ C * B ^ j * Y j ^ (1 + ε)) :
    ∀ j, Y j ≤ δ * q ^ j := by
  intro j
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have hpow : (q ^ j) ^ ε = (q ^ ε) ^ j := by
      rw [← Real.rpow_natCast_mul hq.le, mul_comm (j : ℝ) ε]
      exact Real.rpow_mul_natCast hq.le ε j
    have hid : C * B ^ j * (δ * q ^ j) ^ (1 + ε) =
        δ * q ^ j * (C * δ ^ ε) * (B * q ^ ε) ^ j := by
      rw [Real.rpow_add_of_nonneg (by positivity) (by norm_num) hε.le,
        Real.rpow_one, Real.mul_rpow hδ.le (pow_nonneg hq.le j), hpow, mul_pow]
      ring
    calc
      Y (j + 1) ≤ C * B ^ j * Y j ^ (1 + ε) := hstep j
      _ ≤ C * B ^ j * (δ * q ^ j) ^ (1 + ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hY j) ih (by linarith)) (by positivity)
      _ = δ * q ^ j * (C * δ ^ ε) * (B * q ^ ε) ^ j := hid
      _ ≤ δ * q ^ j * q * 1 := by
        have hlast : (B * q ^ ε) ^ j ≤ 1 := pow_le_one₀ (by positivity) hBq
        gcongr
      _ = δ * q ^ (j + 1) := by rw [pow_succ]; ring

/-- A nonnegative sequence satisfying the nonlinear recurrence tends to zero. -/
theorem nonlinear_iteration_tendsto_zero
    {C B δ q ε : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hq : 0 < q) (hε : 0 < ε)
    (hCδ : C * δ ^ ε ≤ q) (hBq : B * q ^ ε ≤ 1) (hq1 : q < 1)
    {Y : ℕ → ℝ} (hY : ∀ j, 0 ≤ Y j) (h0 : Y 0 ≤ δ)
    (hstep : ∀ j, Y (j + 1) ≤ C * B ^ j * Y j ^ (1 + ε)) :
    Tendsto Y atTop (𝓝 0) := by
  apply squeeze_zero hY
    (nonlinear_iteration_geometric_bound hC hB hδ hq hε hCδ hBq hY h0 hstep)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul δ

/-- The smallness threshold is selected before the sequence. -/
theorem exists_nonlinear_iteration_threshold
    (C B ε : ℝ) (hC : 0 < C) (hB : 1 < B) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : ℕ → ℝ,
      (∀ j, 0 ≤ Y j) → Y 0 ≤ δ →
      (∀ j, Y (j + 1) ≤ C * B ^ j * Y j ^ (1 + ε)) →
      Tendsto Y atTop (𝓝 0) := by
  have hB0 : 0 < B := lt_trans zero_lt_one hB
  let q : ℝ := B ^ (-(1 / ε))
  have hq : 0 < q := Real.rpow_pos_of_pos hB0 _
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hB (neg_neg_of_pos (one_div_pos.mpr hε))
  let δ : ℝ := (q / C) ^ (1 / ε)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (div_pos hq hC) _
  have hδpow : δ ^ ε = q / C := by
    dsimp only [δ]
    rw [← Real.rpow_mul (div_pos hq hC).le]
    have heq : (1 / ε) * ε = 1 := by field_simp
    rw [heq, Real.rpow_one]
  have hqpow : q ^ ε = B⁻¹ := by
    dsimp only [q]
    rw [← Real.rpow_mul hB0.le]
    have heq : (-(1 / ε)) * ε = -1 := by field_simp
    rw [heq, Real.rpow_neg hB0.le, Real.rpow_one]
  have hCδ : C * δ ^ ε ≤ q := by
    rw [hδpow]
    field_simp
    norm_num
  have hBq : B * q ^ ε ≤ 1 := by
    rw [hqpow, mul_inv_cancel₀ hB0.ne']
  refine ⟨δ, hδ, ?_⟩
  intro Y hY h0 hstep
  exact nonlinear_iteration_tendsto_zero hC.le hB0.le hδ hq hε hCδ hBq hq1
    hY h0 hstep

end Yau.LeafProofs.L16DG
