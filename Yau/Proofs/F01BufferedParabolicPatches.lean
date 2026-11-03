import Yau.Proofs.F01AffineHolderRecovery

/-! A fixed spatial and time buffer contains every backward patch
needed by the local Schauder induction, including both time faces. -/
noncomputable section
open Set Metric
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem buffered_backward_patch_maps
    {κ r R a b l s τ : ℝ} {c : Space n}
    (hκ : 0 < κ) (hc : c ∈ ball 0 r) (hτ : τ ∈ Icc l s)
    (hSpace : r + 2 * κ ≤ R) (hLower : a + 4 * κ ^ 2 ≤ l) (hUpper : s ≤ b) :
    MapsTo (fun x => κ • x + c) (ball 0 2) (ball 0 R) ∧
      MapsTo (fun t => τ + κ ^ 2 * t) (Icc (-4) 0) (Icc a b) := by
  constructor
  · intro x hx
    rw [mem_ball, dist_zero_right] at hc hx ⊢
    calc
      ‖κ • x + c‖ ≤ ‖κ • x‖ + ‖c‖ := norm_add_le _ _
      _ = κ * ‖x‖ + ‖c‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
      _ < r + 2 * κ := by nlinarith
      _ ≤ R := hSpace
  · intro t ht
    have hl := mul_le_mul_of_nonneg_left ht.1 (sq_nonneg κ)
    have hu := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg κ)
    dsimp only
    constructor
    · nlinarith [hτ.1]
    · nlinarith [hτ.2]

theorem pair_common_clock_bounds (p q : Point n) :
    0 ≤ max p.2 q.2 - p.2 ∧ max p.2 q.2 - p.2 ≤ |p.2 - q.2| ∧
      0 ≤ max p.2 q.2 - q.2 ∧ max p.2 q.2 - q.2 ≤ |p.2 - q.2| := by
  rcases le_total p.2 q.2 with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith

end Yau.NodeProofs.F01Aux
