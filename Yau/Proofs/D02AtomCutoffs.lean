import Yau.Proofs.D02LimitIdentification
import Yau.Proofs.D02RieszApprox

/-! Actual nonnegative smooth cutoffs shrink to one singleton while all
closed supports remain in a fixed interior disc. -/

open scoped Topology ContDiff
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem exists_atom_cutoffs (z₀ : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ χ : ℕ → ℂ → ℝ,
      (∀ j, ContDiff ℝ ∞ (χ j) ∧ HasCompactSupport (χ j) ∧ tsupport (χ j) ⊆ ball z₀ R) ∧
      (∀ j z, 0 ≤ χ j z ∧ χ j z ≤ 1) ∧
      (∀ j, χ j z₀ = 1) ∧
      ∀ z, Tendsto (fun j => χ j z) atTop (𝓝 (({z₀} : Set ℂ).indicator (fun _ => (1 : ℝ)) z)) := by
  let δ : ℕ → ℝ := fun j => R * (1 / ((j : ℝ) + 1))
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδR (j : ℕ) : δ j ≤ R := by
    have hd : 1 ≤ (j : ℝ) + 1 := by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
    dsimp [δ]
    simpa only [div_one, mul_one] using mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd) hR.le
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul R
  have hc (j : ℕ) := D02RieszAux.exists_smooth_cutoff (U := ball z₀ (δ j))
    isOpen_ball (isCompact_singleton : IsCompact ({z₀} : Set ℂ))
    (singleton_subset_iff.mpr (mem_ball_self (hδ j)))
  choose χ hχ hχc hχsupp hχrange hχone using hc
  refine ⟨χ, fun j => ⟨hχ j, hχc j, (hχsupp j).trans (ball_subset_ball (hδR j))⟩,
    hχrange, fun j => hχone j z₀ (mem_singleton z₀), fun z => ?_⟩
  by_cases hz : z = z₀
  · subst z
    have heq : (fun j => χ j z₀) = fun _ => (1 : ℝ) := funext (fun j => hχone j z₀ (mem_singleton z₀))
    simp only [heq, indicator_of_mem (mem_singleton z₀)]
    exact tendsto_const_nhds
  · have hdist : 0 < dist z z₀ := dist_pos.mpr hz
    have heq : (fun j => χ j z) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [hδlim.eventually (Iio_mem_nhds hdist)] with j hj
      apply image_eq_zero_of_notMem_tsupport
      exact fun hs => (not_lt_of_ge hj.le) (hχsupp j hs)
    rw [indicator_of_notMem (show z ∉ ({z₀} : Set ℂ) from hz)]
    exact tendsto_const_nhds.congr' heq.symm

end Yau.NodeProofs.D02Aux
