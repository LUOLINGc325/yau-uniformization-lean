import Yau.Proofs.D04FiniteL1

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

/-- On a fixed positive-measure overlap an L¹ bound supplies a finite point
with a uniform lower anchor. The point is selected outside the infinite-value
null set before converting back from the real class. -/
theorem exists_point_anchor_of_L1_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {E : Set α}
    (hE : MeasurableSet E) (hμE0 : μ E ≠ 0) (hμEtop : μ E ≠ ⊤)
    {u : α → EReal} (hfinite : ∀ᵐ z ∂μ.restrict E, u z ≠ ⊥ ∧ u z ≠ ⊤)
    (hi : IntegrableOn (fun z => (u z).toReal) E μ)
    {B : ℝ} (hB : (∫ z in E, |(u z).toReal| ∂μ) ≤ B) :
    ∃ z ∈ E, u z ≠ ⊥ ∧ u z ≠ ⊤ ∧
      ((-(B / μ.real E) : ℝ) : EReal) ≤ u z := by
  let : IsFiniteMeasure (μ.restrict E) := isFiniteMeasure_restrict.mpr hμEtop
  let N : Set α := {z | ¬ (z ∈ E ∧ u z ≠ ⊥ ∧ u z ≠ ⊤)}
  have hN : (μ.restrict E) N = 0 := by
    apply ae_iff.mp
    filter_upwards [hfinite, ae_restrict_mem hE] with z hz hzE
    exact ⟨hzE, hz⟩
  obtain ⟨z, hzN, hzavg⟩ := exists_notMem_null_average_le
    (fun h => hμE0 (Measure.restrict_eq_zero.mp h)) hi hN
  have hz : z ∈ E ∧ u z ≠ ⊥ ∧ u z ≠ ⊤ := by simpa only [N, mem_ofPred_eq, not_not] using hzN
  have hmass : 0 < μ.real E := ENNReal.toReal_pos hμE0 hμEtop
  have hint : -B ≤ ∫ z in E, (u z).toReal ∂μ := by
    have hnorm := norm_integral_le_integral_norm (f := fun z => (u z).toReal) (μ := μ.restrict E)
    simp only [Real.norm_eq_abs] at hnorm
    have hlow := (abs_le.mp (hnorm.trans hB)).1
    linarith
  have havg : -(B / μ.real E) ≤ ⨍ z, (u z).toReal ∂μ.restrict E := by
    rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
    simpa only [div_eq_mul_inv, neg_mul, mul_comm] using
      div_le_div_of_nonneg_right hint hmass.le
  refine ⟨z, hz.1, hz.2.1, hz.2.2, ?_⟩
  rw [← EReal.coe_toReal hz.2.2 hz.2.1]
  exact EReal.coe_le_coe_iff.mpr (havg.trans hzavg)

end Yau.Proofs.D04Aux
