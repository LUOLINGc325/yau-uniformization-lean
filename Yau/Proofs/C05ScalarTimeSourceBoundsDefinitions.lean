import Mathlib

/-! Explicit dimensional budgets, chosen solely from the same-point scalar and Ricci jet bound. -/
noncomputable section
namespace Yau.Proofs.C05ScalarTimeSourceBoundsAux

def realDimension (n : ℕ) : ℝ := (2*n:ℕ)

def b1 (n : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt (realDimension n) / 2 * B + 16 * realDimension n * B^2

def b2 (n : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt (realDimension n) / 2 * b1 n B + 12 * realDimension n * B^2 +
    128 * (realDimension n + 1)^3 * B^3

def b3 (n : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt (realDimension n) / 2 * b2 n B + 2 * B * b1 n B +
    12 * (realDimension n + 1)^2 * B^3 + 3 * (realDimension n + 1)^2 * B^2 +
    6 * (realDimension n + 1)^2 * B^4

theorem b1_nonneg (n : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ b1 n B := by
  unfold b1 realDimension
  positivity

theorem b2_nonneg (n : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ b2 n B := by
  unfold b2 b1 realDimension
  positivity

theorem b3_nonneg (n : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ b3 n B := by
  unfold b3 b2 b1 realDimension
  positivity

end Yau.Proofs.C05ScalarTimeSourceBoundsAux
