import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

open scoped BigOperators

namespace Yau.LeafProofs.L05AutonomousAux

/-- The positive weighted secant identity controls every actual deficit. -/
theorem finite_deficit_comparison {m : ℕ} {a b : ℝ} (ha : 0 < a)
    (_hab : a ≤ b) (M x y c : Fin m → ℝ)
    (hx : ∀ i, x i ≤ M i) (hy : ∀ i, y i ≤ M i)
    (hc : ∀ i, c i ∈ Set.Icc a b)
    (heq : ∑ i, c i * (x i - y i) = 0) (j : Fin m) :
    M j - x j ≤ (b / a) * ∑ i, (M i - y i) := by
  have hsum : ∑ i, c i * (M i - x i) = ∑ i, c i * (M i - y i) := by
    have : (∑ i, c i * (M i - y i)) - (∑ i, c i * (M i - x i)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      convert heq using 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    linarith
  have hleft : a * (M j - x j) ≤ ∑ i, c i * (M i - x i) := by
    calc
      _ ≤ c j * (M j - x j) := mul_le_mul_of_nonneg_right (hc j).1 (sub_nonneg.mpr (hx j))
      _ ≤ _ := Finset.single_le_sum (fun i _ => mul_nonneg
        (ha.le.trans (hc i).1) (sub_nonneg.mpr (hx i))) (Finset.mem_univ j)
  have hright : (∑ i, c i * (M i - y i)) ≤ b * ∑ i, (M i - y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (hc i).2 (sub_nonneg.mpr (hy i))
  have h : a * (M j - x j) ≤ b * ∑ i, (M i - y i) := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).2
  nlinarith [h]

/-- Subadditivity of a nonnegative finite family raised to an exponent at most one. -/
theorem finite_sum_rpow_le {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, u i) ^ p ≤ ∑ i ∈ s, (u i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp.ne']
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (Real.rpow_add_le_add_rpow (hu i (by simp))
      (Finset.sum_nonneg fun j hj => hu j (by simp [hj])) hp.le hp1).trans
      (add_le_add (le_refl _) (ih fun j hj => hu j (by simp [hj])))

end Yau.LeafProofs.L05AutonomousAux
