import Yau.Proofs.D04Majorants

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

/-- The increasing negative deficits retain a genuine infinite value at a
minus-infinity pole; no `toReal` of that pole is substituted for it. -/
def deficitSup (C : ℝ) (a : EReal) : ENNReal :=
  ⨆ k : ℕ, ENNReal.ofReal (C - (max a ((-(k : ℝ) : ℝ) : EReal)).toReal)

theorem deficitSup_bot (C : ℝ) : deficitSup C ⊥ = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro m
  obtain ⟨k, hk⟩ := exists_nat_gt ((m : ℝ) - C)
  have hmk : (m : ENNReal) ≤ ENNReal.ofReal (C + k) := by
    rw [← ENNReal.ofReal_natCast m]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact hmk.trans (by
    simpa only [deficitSup, max_eq_right bot_le, EReal.toReal_coe, sub_neg_eq_add]
      using (le_iSup (fun k : ℕ => ENNReal.ofReal
        (C - (max (⊥ : EReal) ((-(k : ℝ) : ℝ) : EReal)).toReal)) k))

theorem ofReal_sub_toReal_le_deficitSup (C : ℝ) {a : EReal}
    (hatop : a ≠ ⊤) (habot : a ≠ ⊥) :
    ENNReal.ofReal (C - a.toReal) ≤ deficitSup C a := by
  obtain ⟨k, hk⟩ := exists_nat_ge (-a.toReal)
  have hka : ((-(k : ℝ) : ℝ) : EReal) ≤ a := by
    rw [← EReal.coe_toReal hatop habot]
    apply EReal.coe_le_coe_iff.mpr
    linarith
  have h := le_iSup (fun k : ℕ => ENNReal.ofReal
    (C - (max a ((-(k : ℝ) : ℝ) : EReal)).toReal)) k
  simpa only [deficitSup, max_eq_left hka] using h

/-- A uniform bound for the actual truncated negative parts proves both
finiteness almost everywhere and local integrability of the same real class.
In particular, bottom is excluded before the real-valued pairing is used. -/
theorem finiteL1_of_truncation_deficit_bound
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) {K : Set α} (hK : MeasurableSet K) (hμK : μ K < ⊤)
    {u : α → EReal} (hu : UpperSemicontinuousOn u K)
    {C : ℝ} (hC : ∀ z ∈ K, u z ≤ (C : EReal))
    {D : ENNReal} (hD : D ≠ ⊤)
    (hbound : ∀ k : ℕ, (∫⁻ z in K, ENNReal.ofReal (C - lowerTrunc u k z) ∂μ) ≤ D) :
    (∀ᵐ z ∂μ.restrict K, u z ≠ ⊥ ∧ u z ≠ ⊤) ∧
      IntegrableOn (fun z => (u z).toReal) K μ := by
  have hf (k : ℕ) : AEMeasurable
      (fun z => ENNReal.ofReal (C - lowerTrunc u k z)) (μ.restrict K) :=
    (aemeasurable_const.sub
      (integrableOn_lowerTrunc μ hK hμK hu hC k).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hmono : ∀ᵐ z ∂μ.restrict K,
      Monotone (fun k : ℕ => ENNReal.ofReal (C - lowerTrunc u k z)) := by
    filter_upwards [ae_restrict_mem hK] with z hz
    intro i j hij
    apply ENNReal.ofReal_le_ofReal
    exact sub_le_sub_left
      (lowerTrunc_antitone ((hC z hz).trans_lt (EReal.coe_lt_top C)) hij) C
  have hFm : AEMeasurable (fun z => deficitSup C (u z)) (μ.restrict K) :=
    AEMeasurable.iSup hf
  have hInt : (∫⁻ z in K, deficitSup C (u z) ∂μ) ≤ D := by
    change (∫⁻ z, ⨆ k : ℕ, ENNReal.ofReal (C - lowerTrunc u k z) ∂μ.restrict K) ≤ D
    rw [lintegral_iSup' hf hmono]
    exact iSup_le hbound
  have hFfinite : ∀ᵐ z ∂μ.restrict K, deficitSup C (u z) < ⊤ :=
    ae_lt_top' hFm (ne_top_of_le_ne_top hD hInt)
  have hfinite : ∀ᵐ z ∂μ.restrict K, u z ≠ ⊥ ∧ u z ≠ ⊤ := by
    filter_upwards [hFfinite, ae_restrict_mem hK] with z hz hzK
    refine ⟨?_, ((hC z hzK).trans_lt (EReal.coe_lt_top C)).ne⟩
    intro hbot
    rw [hbot, deficitSup_bot] at hz
    exact lt_irrefl _ hz
  refine ⟨hfinite, ?_⟩
  have hFreal : Integrable (fun z => (deficitSup C (u z)).toReal) (μ.restrict K) :=
    integrable_toReal_of_lintegral_ne_top hFm (ne_top_of_le_ne_top hD hInt)
  have hureal : AEMeasurable (fun z => (u z).toReal) (μ.restrict K) :=
    (aemeasurable_restrict_of_measurable_subtype hK
      (upperSemicontinuousOn_iff_restrict.mpr hu).measurable).ereal_toReal
  apply ((integrableOn_const hμK.ne (C := |C|)).add hFreal).mono' hureal.aestronglyMeasurable
  filter_upwards [hfinite, hFfinite, ae_restrict_mem hK] with z hz hzF hzK
  have hzC : (u z).toReal ≤ C := by
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal hz.2 hz.1]
    exact hC z hzK
  have hdef := ENNReal.toReal_mono hzF.ne
    (ofReal_sub_toReal_le_deficitSup C hz.2 hz.1)
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hzC)] at hdef
  rw [Real.norm_eq_abs]
  change |(u z).toReal| ≤ |C| + (deficitSup C (u z)).toReal
  apply abs_le.mpr
  exact ⟨by linarith [neg_abs_le C],
    by linarith [le_abs_self C, ENNReal.toReal_nonneg (a := deficitSup C (u z))]⟩

end Yau.Proofs.D04Aux
