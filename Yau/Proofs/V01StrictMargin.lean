import Yau.Proofs.V01QuadraticSupport

/-! V01 scratch source: strictness and the compact-frontier gap are derived
from the explicit quadratic margin. No envelope minimizer is asserted. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

theorem coordinateSquare_pos_of_ne
    {a y : ComplexVector n × ComplexVector n × ℝ} (hy : y ≠ a) :
    0 < coordinateSquare a y := by
  by_contra! hn
  have hzero : coordinateSquare a y = 0 :=
    le_antisymm hn (coordinateSquare_nonneg a y)
  exact hy ((coordinateSquare_eq_zero_iff a y).mp hzero)

theorem strict_lower_of_quadratic_margin
    {a y : ComplexVector n × ComplexVector n × ℝ}
    {ψ f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {v : ComplexVector n × ComplexVector n × ℝ → EReal}
    {α : ℝ} (hα : 0 < α) (hy : y ≠ a)
    (hmargin : ψ y + (α / 2) * coordinateSquare a y ≤ f y)
    (hfv : (f y : EReal) ≤ v y) : (ψ y : EReal) < v y := by
  have hpos := mul_pos (half_pos hα) (coordinateSquare_pos_of_ne hy)
  have hlt : ψ y < f y := by linarith
  exact (EReal.coe_lt_coe_iff.mpr hlt).trans_le hfv

theorem touch_iff_of_quadratic_margin
    {a y : ComplexVector n × ComplexVector n × ℝ}
    {ψ f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {v : ComplexVector n × ComplexVector n × ℝ → EReal}
    {α : ℝ} (hα : 0 < α) (hψa : ψ a = f a) (hfa : (f a : EReal) = v a)
    (hmargin : ψ y + (α / 2) * coordinateSquare a y ≤ f y)
    (hfv : (f y : EReal) ≤ v y) :
    (ψ y : EReal) = v y ↔ y = a := by
  constructor
  · intro heq
    by_contra hne
    exact (ne_of_lt (strict_lower_of_quadratic_margin hα hne hmargin hfv)) heq
  · rintro rfl
    simpa only [hψa] using hfa

theorem exists_uniform_quadratic_gap
    (a : ComplexVector n × ComplexVector n × ℝ)
    (K : Set (ComplexVector n × ComplexVector n × ℝ))
    (hK : IsCompact K) (ha : a ∉ K) {α : ℝ} (hα : 0 < α) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ y ∈ K,
      gap ≤ (α / 2) * coordinateSquare a y := by
  by_cases hne : K.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne
      (coordinateSquare_contDiff a).continuous.continuousOn
    have hya : y ≠ a := by
      rintro rfl
      exact ha hy
    refine ⟨(α / 2) * coordinateSquare a y,
      mul_pos (half_pos hα) (coordinateSquare_pos_of_ne hya), ?_⟩
    intro z hz
    exact mul_le_mul_of_nonneg_left (hmin hz) (half_pos hα).le
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    exact (hne ⟨y, hy⟩).elim

end Yau.Blueprint.V01Proof
