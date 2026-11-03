import Mathlib

/-! Scalar budgets for backward iteration in the original inverse tubes. -/
open Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.U01Proof

theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  rw [Real.exp_neg]
  exact inv_le_of_inv_le₀ (by norm_num) (by convert Real.add_one_le_exp (1 : ℝ) using 1 <;> norm_num)

theorem inverse_budget {u t delta : ℝ} (hu : 1 ≤ u)
    (hgap : 1 ≤ t - u) (hupper : t ≤ (1 + delta) * u)
    (hd : delta < 1 / 10) :
    Real.exp (t - u) * (Real.exp (-7 * t) + Real.exp (-10 * u)) ≤
      Real.exp (-7 * u) := by
  have hud : delta * u ≤ (1 / 10 : ℝ) * u :=
    mul_le_mul_of_nonneg_right hd.le (by linarith)
  have h1 : Real.exp (-6 * (t - u)) ≤ (1 / 2 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_neg_one_le_half
  have h2 : Real.exp (t - 4 * u) ≤ (1 / 2 : ℝ) :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans exp_neg_one_le_half
  calc
    _ = Real.exp (-7 * u) *
        (Real.exp (-6 * (t - u)) + Real.exp (t - 4 * u)) := by
      rw [mul_add, mul_add, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add]
      congr 1 <;> ring
    _ ≤ Real.exp (-7 * u) * (1 / 2 + 1 / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.exp_pos _).le
    _ = _ := by ring

theorem tube_budget {u t nu delta : ℝ} (hu : 0 ≤ u)
    (ht : 0 ≤ t) (hn : 0 < nu) (hn' : nu < 1 / 10)
    (hd : delta < 1 / 10) (hupper : t ≤ (1 + delta) * u)
    (hsmall : Real.exp (-nu * t) < 1 / 2) :
    Real.exp (-2 * nu * t) + Real.exp (-7 * t) < Real.exp (-nu * t) ∧
    Real.exp (-2 * nu * t) + Real.exp (-10 * u) < Real.exp (-nu * t) := by
  have hq : Real.exp (-7 * t) ≤ Real.exp (-2 * nu * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdu : delta * u ≤ (1 / 10 : ℝ) * u := mul_le_mul_of_nonneg_right hd.le hu
  have hnt : nu * t ≤ (1 / 10 : ℝ) * t := mul_le_mul_of_nonneg_right hn'.le ht
  have he : Real.exp (-10 * u) ≤ Real.exp (-2 * nu * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have heq : Real.exp (-2 * nu * t) = Real.exp (-nu * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hh : 2 * Real.exp (-2 * nu * t) < Real.exp (-nu * t) := by
    rw [heq]
    nlinarith [Real.exp_pos (-nu * t)]
  constructor <;> linarith

theorem exp_decay {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun k => Real.exp (-a * s k)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hs.const_mul_atTop ha)

end Yau.NodeProofs.U01Proof
