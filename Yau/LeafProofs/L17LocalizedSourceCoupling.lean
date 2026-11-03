import Yau.LeafProofs.L17SourceLocalization

/-! The actual transported local forcing has exactly the partition-of-unity total source. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17Aux

open L17HolderAux L17SourceLocalizationAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def transportedLocalizedSource (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Cylinder M T) : ℝ := by
  classical
  exact if q.1 ∈ (P.charts.chart p).target then
    localizedSource P T hT f p ((P.charts.chart p).symm q.1,(q.2 : ℝ)) else 0

theorem localizedSource_partition_coupling
    (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T) {γ : ℝ}
    (f : HolderSpace P T γ) (p : P.centers) (q : Cylinder M T) :
    P.localization p q.1 * transportedLocalizedSource P T hT f p q =
      P.weight p q.1 * holderFun f q := by
  classical
  let e := P.charts.chart p
  have hsupp : tsupport (P.weight p) ⊆ e '' closedBall (0 : ComplexVector n) (P.radius / 2) :=
    (normalizedChartWeight_tsupport_subset P.charts P.centers P.radius_pos p).trans
      (P.charts.chartWeight_properties p P.radius_pos P.radius_lt).2.2
  have hsource : closedBall (0 : ComplexVector n) (P.radius / 2) ⊆ e.source := by
    intro z hz
    exact P.charts.closedBall_source p
      ((closedBall_subset_closedBall (by have := P.radius_pos; have := P.radius_lt; linarith)) hz)
  by_cases ht : q.1 ∈ e.target
  · by_cases hz : e.symm q.1 ∈ ball (0 : ComplexVector n) P.radius
    · have hformula := localizedSource_formula P T hT f p hz q.2.property
      rw [show P.charts.chart p (e.symm q.1) = q.1 from e.right_inv ht] at hformula
      change P.localization p q.1 * (if q.1 ∈ e.target then
        localizedSource P T hT f p (e.symm q.1, (q.2 : ℝ)) else 0) = _
      rw [ite_eq_left ht, hformula, ← mul_assoc, P.localization_mul_weight]
    · have hw : P.weight p q.1 = 0 := by
        by_contra hn
        obtain ⟨z, hzb, hzx⟩ := hsupp (subset_tsupport _ hn)
        have hInv : e.symm q.1 = z := by rw [← hzx, e.left_inv (hsource hzb)]
        have hzin : z ∈ ball (0 : ComplexVector n) P.radius :=
          (closedBall_subset_ball (by have := P.radius_pos; linarith)) hzb
        exact hz (by rw [hInv]; exact hzin)
      change P.localization p q.1 * (if q.1 ∈ e.target then
        localizedSource P T hT f p (e.symm q.1, (q.2 : ℝ)) else 0) = _
      rw [ite_eq_left ht]
      simp only [localizedSource, hz, ite_false, hw, mul_zero, zero_mul]
  · have hw : P.weight p q.1 = 0 := by
      by_contra hn
      obtain ⟨z, hzb, hzx⟩ := hsupp (subset_tsupport _ hn)
      exact ht (hzx ▸ e.map_source (hsource hzb))
    change P.localization p q.1 * (if q.1 ∈ e.target then
      localizedSource P T hT f p (e.symm q.1, (q.2 : ℝ)) else 0) = _
    rw [ite_eq_right ht, hw, mul_zero, zero_mul]

theorem localizedSource_partition_sum
    (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T) {γ : ℝ}
    (f : HolderSpace P T γ) (q : Cylinder M T) :
    (∑ᶠ p : P.centers, P.localization p q.1 * transportedLocalizedSource P T hT f p q) =
      holderFun f q := by
  simp_rw [localizedSource_partition_coupling]
  rw [← finsum_mul, P.weight_sum, one_mul]

end Yau.LeafProofs.L17Aux
