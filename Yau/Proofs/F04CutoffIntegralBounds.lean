import Yau.Proofs.F04SpatialCutoff
import Yau.Proofs.F04InitialEnergyValue

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem cylinder_measure_real {n : ℕ} (O : Set (Space n)) {a b : ℝ} (hab : a ≤ b) :
    (productVolume O (Ioo a b)).real univ = volume.real O * (b - a) := by
  rw [productVolume, ← univ_prod_univ, measureReal_prod_prod,
    measureReal_restrict_apply_univ, measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le hab]

theorem timeConstant_cutoff_integral_bounds {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hOc : IsCompact (closure O)) {s δ K M : ℝ}
    (hδ : δ ∈ Ioo 0 s) (hK : 0 ≤ K) (hM : 0 ≤ M) {u : Point n → ℝ} {η : Space n → ℝ}
    (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηM : ∀ x, (∑ i, (d η x i) ^ 2) + (η x) ^ 2 ≤ M)
    (hbound : ∀ x ∈ O, ∀ t ∈ Ioo 0 s, |u (x, t)| ≤ K * t) :
    dgCylinderIntegral O δ s (cutoffValueError u (fun p => η p.1)) ≤
        (K * s) ^ 2 * M * volume.real O * s ∧
      (∫ x in O, (u (x, δ)) ^ 2 * (η x) ^ 2) ≤ (K * δ) ^ 2 * volume.real O := by
  have hOfin : volume O < ⊤ := (measure_mono subset_closure).trans_lt hOc.measure_lt_top
  have : IsFiniteMeasure (volume.restrict O) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hOfin⟩
  have : IsFiniteMeasure (volume.restrict (Ioo δ s)) := ⟨by simp⟩
  have : IsFiniteMeasure (productVolume O (Ioo δ s)) := inferInstanceAs
    (IsFiniteMeasure ((volume.restrict O).prod (volume.restrict (Ioo δ s))))
  have huabs (x : Space n) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Ioo δ s) : |u (x, t)| ≤ K * s :=
    (hbound x hx t ⟨hδ.1.trans ht.1, ht.2⟩).trans (mul_le_mul_of_nonneg_left ht.2.le hK)
  have hQ0 (x : Space n) : 0 ≤ (∑ i, (d η x i) ^ 2) + (η x) ^ 2 :=
    add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
  have hnorm : ∀ᵐ p ∂productVolume O (Ioo δ s),
      ‖cutoffValueError u (fun q => η q.1) p‖ ≤ (K * s) ^ 2 * M := by
    rw [dg_productVolume_eq_restrict]
    filter_upwards [ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet] with p hp
    have hu2 : (u p) ^ 2 ≤ (K * s) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (huabs p.1 hp.1 p.2 hp.2) 2
    dsimp only [cutoffValueError]
    simp only [deriv_const, abs_zero, zero_add]
    change ‖(u p) ^ 2 * ((∑ i, (d η p.1 i) ^ 2) + (η p.1) ^ 2)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hQ0 p.1))]
    exact mul_le_mul hu2 (hηM p.1) (hQ0 p.1) (sq_nonneg _)
  constructor
  · have hh := (le_abs_self (dgCylinderIntegral O δ s (cutoffValueError u (fun p => η p.1)))).trans
      (norm_integral_le_of_norm_le_const hnorm)
    rw [cylinder_measure_real O hδ.2.le] at hh
    apply hh.trans
    have hscale : 0 ≤ (K * s) ^ 2 * M * volume.real O := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left (sub_le_self s hδ.1.le) hscale]
  · have hnorm0 : ∀ᵐ x ∂volume.restrict O, ‖(u (x, δ)) ^ 2 * (η x) ^ 2‖ ≤ (K * δ) ^ 2 := by
      filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
      have hu2 : (u (x, δ)) ^ 2 ≤ (K * δ) ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound x hx δ hδ) 2
      have hη2 : (η x) ^ 2 ≤ 1 := by
        have hh := hηrange x
        nlinarith [hh.1, hh.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      simpa only [mul_one] using mul_le_mul hu2 hη2 (sq_nonneg _) (sq_nonneg _)
    have hh := (le_abs_self (∫ x in O, (u (x, δ)) ^ 2 * (η x) ^ 2)).trans
      (norm_integral_le_of_norm_le_const hnorm0)
    simpa only [measureReal_restrict_apply_univ] using hh

end Yau.F04Proof
