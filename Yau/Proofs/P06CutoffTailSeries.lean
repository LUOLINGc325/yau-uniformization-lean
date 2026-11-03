import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
open Filter Finset
open scoped Topology

namespace Yau.NodeProofs.P06Aux.CutoffTail

/-- The radii of the fixed dyadic annular decomposition. -/
def radius (m : ℕ) : ℝ := 2 ^ m

theorem radius_pos (m : ℕ) : 0 < radius m := by
  unfold radius
  positivity

theorem one_le_radius (m : ℕ) : 1 ≤ radius m := one_le_pow₀ (by norm_num)

theorem radius_mono : Monotone radius := by
  exact fun _ _ h => pow_le_pow_right₀ (by norm_num) h

theorem radius_succ (m : ℕ) : radius (m + 1) = 2 * radius m := by
  simp only [radius, pow_succ, mul_comm]

theorem radius_tendsto : Tendsto radius atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

/-- Polynomial volume growth is summable against the dyadic exponential
majorant of the Gaussian heat tail. -/
theorem summable_dyadic (d : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun m : ℕ => radius m ^ d * Real.exp (-a * radius m)) := by
  have h := (Real.summable_pow_mul_exp_neg_nat_mul d ha).comp_injective
    (Nat.pow_right_injective (show 2 ≤ (2 : ℕ) by decide))
  simpa only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat, radius] using h

/-- Every finite collection of sufficiently remote annuli has arbitrarily
small total majorant; the collection may depend on both cutoff indices. -/
theorem exists_small_finite_dyadic_tail (d : ℕ) {a : ℝ} (ha : 0 < a)
    (C : ℝ) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, (∀ m ∈ s, N ≤ m) →
      ∑ m ∈ s, C * (radius m ^ d * Real.exp (-a * radius m)) < ε := by
  have hs := (summable_dyadic d ha).mul_left C
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hs ε hε
  refine ⟨s.sup id + 1, fun t ht => ?_⟩
  have hd : Disjoint t s := by
    apply Finset.disjoint_left.mpr
    intro m hmt hms
    have hle : m ≤ s.sup id := Finset.le_sup (f := id) hms
    have hge := ht m hmt
    omega
  have hh := hs t hd
  rw [Real.norm_eq_abs, abs_of_nonneg] at hh
  · exact hh
  · exact Finset.sum_nonneg fun m hm => mul_nonneg hC
      (mul_nonneg (pow_nonneg (radius_pos m).le _) (Real.exp_pos _).le)

/-- A Gaussian at any time in the fixed initial slab admits a single
exponential dyadic majorant, once the inner ball is separated by a factor two. -/
theorem gaussian_le_exponential {A T t r R : ℝ}
    (hA : 0 < A) (hT : 0 < T) (ht : 0 < t) (htT : t ≤ T)
    (hR : 1 ≤ R) (hsep : 2 * r ≤ R) :
    Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) ≤
      Real.exp (-(1 / (8 * A ^ 2 * T)) * R) := by
  apply Real.exp_le_exp.mpr
  have hden : 0 < 2 * A ^ 2 * t := by positivity
  have hdenT : 0 < 8 * A ^ 2 * T := by positivity
  apply (div_le_iff₀ hden).mpr
  have hsq : R ≤ 4 * (R - r) ^ 2 := by
    have : 0 ≤ R - r := by linarith
    nlinarith [sq_nonneg (R - r), mul_self_le_mul_self (by positivity : 0 ≤ R / 2)
      (by linarith : R / 2 ≤ R - r)]
  have hmul : R * (2 * A ^ 2 * t) ≤
      (R - r) ^ 2 * (8 * A ^ 2 * T) := by
    have h₁ := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ 2 * A ^ 2 * t)
    have h₂ := mul_le_mul_of_nonneg_left htT
      (by positivity : 0 ≤ 8 * A ^ 2 * (R - r) ^ 2)
    nlinarith
  have hh := (div_le_iff₀ hdenT).mpr hmul
  convert neg_le_neg hh using 1 <;> field_simp <;> ring

end Yau.NodeProofs.P06Aux.CutoffTail
