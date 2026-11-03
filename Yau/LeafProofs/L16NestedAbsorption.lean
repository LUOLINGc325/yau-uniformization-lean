import Yau.Blueprint.ParabolicSpaces

open Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic

/-- The closed backward cylinder used to hold the initial pointwise bound. -/
def closedBackwardCylinder {n : ℕ} (R : ℝ) : Set (Point n) :=
  cylinder (Metric.closedBall 0 R) (-(R ^ 2)) 0

theorem closedBackwardCylinder_mono {n : ℕ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    closedBackwardCylinder (n := n) r ⊆ closedBackwardCylinder R := by
  intro z hz
  rcases hz with ⟨hx, ht⟩
  refine ⟨Metric.closedBall_subset_closedBall hrR hx, ?_, ht.2⟩
  have hsq : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr hrR 2
  linarith [ht.1]

/-- Finite nested-cylinder iteration absorbs a pointwise high bound. The only
analytic input is the displayed one-step estimate; the initial bound is an
actual pointwise bound on the largest closed cylinder. -/
theorem nested_high_bound_absorption {n : ℕ} {J : Point n → ℝ} {P : ℕ}
    {A D Kstar : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ Kstar)
    (hBound : ∀ z ∈ closedBackwardCylinder (n := n) (3 / 2), J z ≤ Kstar)
    (hStep : ∀ r R K : ℝ, 1 ≤ r → r < R → R ≤ 3 / 2 → 0 ≤ K →
      (∀ z ∈ closedBackwardCylinder (n := n) R, J z ≤ K) →
      ∀ z ∈ closedBackwardCylinder (n := n) r,
        J z ≤ (2 ^ (P + 1) : ℝ)⁻¹ * K + A * ((R - r)⁻¹) ^ P * D) :
    ∀ z ∈ closedBackwardCylinder (n := n) (5 / 4),
      J z ≤ 2 * A * (8 : ℝ) ^ P * D := by
  let θ : ℝ := (2 ^ (P + 1) : ℝ)⁻¹
  let q : ℝ := (2 : ℝ) ^ P
  let r : ℕ → ℝ := fun j => 3 / 2 - ((2 : ℝ) ^ j)⁻¹ / 4
  let C : ℕ → ℝ := fun j => A * (8 : ℝ) ^ P * q ^ j * D
  have hq : 1 ≤ q := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
  have hθq : θ * q = 1 / 2 := by
    dsimp only [θ, q]
    rw [pow_succ]
    field_simp
  have hθ1 : θ < 1 := by nlinarith
  have hC (j : ℕ) : 0 ≤ C j := by dsimp only [C, q]; positivity
  have hCsucc (j : ℕ) : θ * C (j + 1) = C j / 2 := by
    dsimp only [C]
    rw [pow_succ]
    calc
      θ * (A * 8 ^ P * (q ^ j * q) * D) =
          (θ * q) * (A * 8 ^ P * q ^ j * D) := by ring
      _ = _ := by rw [hθq]; ring
  have hrLower (j : ℕ) : 1 ≤ r j := by
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hinv : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow
    dsimp only [r]
    linarith
  have hrUpper (j : ℕ) : r j < 3 / 2 := by
    have hinv : 0 < ((2 : ℝ) ^ j)⁻¹ := by positivity
    dsimp only [r]
    linarith
  have hgap (j : ℕ) : r (j + 1) - r j = (8 * (2 : ℝ) ^ j)⁻¹ := by
    dsimp only [r]
    rw [pow_succ]
    field_simp
    ring
  have hrStep (j : ℕ) : r j < r (j + 1) := by
    have hpos : 0 < (8 * (2 : ℝ) ^ j)⁻¹ := by positivity
    linarith [hgap j]
  have hcost (j : ℕ) : A * ((r (j + 1) - r j)⁻¹) ^ P * D = C j := by
    rw [hgap, inv_inv, mul_pow, ← pow_mul, Nat.mul_comm j P, pow_mul]
    dsimp only [C, q]
    ring
  have hfinite (N : ℕ) : ∀ j : ℕ,
      ∀ z ∈ closedBackwardCylinder (n := n) (r j),
        J z ≤ θ ^ N * Kstar + 2 * C j := by
    induction N with
    | zero =>
        intro j z hz
        have hJ := hBound z (closedBackwardCylinder_mono
          (by linarith [hrLower j]) (hrUpper j).le hz)
        simpa only [pow_zero, one_mul] using
          hJ.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) (hC j)))
    | succ N ih =>
        intro j z hz
        have hBudget : 0 ≤ θ ^ N * Kstar + 2 * C (j + 1) := by positivity
        have hJ := hStep (r j) (r (j + 1))
          (θ ^ N * Kstar + 2 * C (j + 1)) (hrLower j) (hrStep j)
          (hrUpper (j + 1)).le hBudget (ih (j + 1)) z hz
        change J z ≤ θ * (θ ^ N * Kstar + 2 * C (j + 1)) +
          A * ((r (j + 1) - r j)⁻¹) ^ P * D at hJ
        rw [hcost] at hJ
        calc
          J z ≤ θ * (θ ^ N * Kstar + 2 * C (j + 1)) + C j := hJ
          _ = θ ^ (N + 1) * Kstar + 2 * C j := by
            rw [pow_succ]
            nlinarith [hCsucc j]
  intro z hz
  have hz0 : z ∈ closedBackwardCylinder (n := n) (r 0) := by
    norm_num [r] at ⊢
    exact hz
  have hlimit : Tendsto (fun N : ℕ => θ ^ N * Kstar + 2 * C 0)
      atTop (𝓝 (2 * C 0)) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const Kstar).add_const
      (2 * C 0)
  have hJ : J z ≤ 2 * C 0 := ge_of_tendsto hlimit (Eventually.of_forall
    (fun N => hfinite N 0 z hz0))
  simpa only [C, pow_zero, mul_one, one_mul, mul_assoc] using hJ

end Yau.LeafProofs.L16Aux
