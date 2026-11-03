import Yau.Proofs.F04ClassicalWeakGradient

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem signed_gradient_square {ι : Type*} [Fintype ι] (r : ℝ) (G : ι → ℝ)
    (hz : r = 0 → ∀ i, G i = 0) :
    (∑ i, (G i) ^ 2) =
      (∑ i, (if 0 < r then G i else 0) ^ 2) +
      ∑ i, (if 0 < -r then -G i else 0) ^ 2 := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · simp only [not_lt.mpr hr.le, ite_false, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, zero_add, neg_pos.mpr hr, ite_true, neg_sq]
  · simp only [hz hr, neg_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ite_self, Finset.sum_const_zero, zero_add]
  · simp only [hr, ite_true, not_lt.mpr (neg_nonpos.mpr hr.le), ite_false,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, add_zero]

/-- Both signs recover the full classical gradient, retaining the zero level
through the genuine almost-everywhere derivative theorem. -/
theorem cutoff_gradient_split_ae {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r a b : ℝ} (hla : l < a) (hbr : b < r)
    {u ζ : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo l r))
    (hζ : DGSpatialCutoff O a b ζ) :
    ∀ᵐ z ∂productVolume O (Ioo a b),
      dgGradientSq (dgGradient u z) * (ζ z) ^ 2 =
        dgTruncationEnergyDensity 1 0 u ζ z + dgTruncationEnergyDensity (-1) 0 u ζ z := by
  obtain ⟨K, hK, hKO, hζzero⟩ := hζ.2.2
  have hU : IsOpen (O ×ˢ Ioo l r) := hO.prod isOpen_Ioo
  have hKU : K ×ˢ Icc a b ⊆ O ×ˢ Ioo l r :=
    fun z hz => ⟨hKO hz.1, hla.trans_le hz.2.1, hz.2.2.trans_lt hbr⟩
  obtain ⟨w, hw, hcw, hwu⟩ := dg_smooth_compact_extension hU (hK.prod isCompact_Icc) hKU hu
  obtain ⟨C, hC⟩ := hw.lipschitzWith_of_hasCompactSupport hcw (by simp)
  have : (volume : Measure (Point n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hzero := dg_fderiv_zero_ae_on_level (μ := (volume : Measure (Point n))) hC 0
  rw [dg_productVolume_eq_restrict]
  filter_upwards [hzero.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet] with z hz hzQ
  by_cases hzK : z.1 ∈ K
  · have hzKQ : z ∈ K ×ˢ Icc a b := ⟨hzK, Ioo_subset_Icc_self hzQ.2⟩
    have hzU := hKU hzKQ
    have hgz : u z = 0 → ∀ i, dgGradient u z i = 0 := by
      intro huz i
      have hwz : w z = 0 := (hwu z hzKQ).eq_of_nhds.trans huz
      rw [dgGradient_eq_joint_fderiv ((hu.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)) i,
        ← (hwu z hzKQ).fderiv_eq, hz hwz]
      rfl
    have hh := signed_gradient_square (u z) (dgGradient u z) hgz
    dsimp only [dgTruncationEnergyDensity, dgGradientSq, dgTruncationGradient]
    simp only [one_mul, neg_one_mul] at *
    nlinarith only [congrArg (fun t : ℝ => t * (ζ z) ^ 2) hh]
  · dsimp only [dgTruncationEnergyDensity]
    rw [hζzero z (Ioo_subset_Icc_self hzQ.2) hzK]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add]

end Yau.F04Proof
