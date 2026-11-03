import Yau.Proofs.F04GradientSplit

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem signed_positive_square (r : ℝ) :
    (dgPositivePart r) ^ 2 + (dgPositivePart (-r)) ^ 2 = r ^ 2 := by
  rcases le_total 0 r with hr | hr
  · rw [dgPositivePart_of_nonneg hr, dgPositivePart_of_nonpos (neg_nonpos.mpr hr), zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  · rw [dgPositivePart_of_nonpos hr, dgPositivePart_of_nonneg (neg_nonneg.mpr hr), zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, neg_sq]

def cutoffValueError {n : ℕ} (u ζ : Point n → ℝ) (z : Point n) : ℝ :=
  (u z) ^ 2 * (|deriv (fun t => ζ (z.1, t)) z.2| +
    dgGradientSq (dgGradient ζ z) + (ζ z) ^ 2)

theorem signed_cutoff_error {n : ℕ} (u ζ : Point n → ℝ) (z : Point n) :
    dgTruncationCutoffError 1 0 u ζ z + dgTruncationCutoffError (-1) 0 u ζ z =
      cutoffValueError u ζ z := by
  dsimp only [dgTruncationCutoffError, dgTruncation, cutoffValueError]
  simp only [one_mul, neg_one_mul, sub_zero]
  rw [← add_mul, signed_positive_square]

theorem signed_slice_square {n : ℕ} (u ζ : Point n → ℝ) (z : Point n) :
    (dgTruncation 1 0 u z) ^ 2 * (ζ z) ^ 2 +
      (dgTruncation (-1) 0 u z) ^ 2 * (ζ z) ^ 2 = (u z) ^ 2 * (ζ z) ^ 2 := by
  dsimp only [dgTruncation]
  simp only [one_mul, neg_one_mul, sub_zero]
  rw [← add_mul, signed_positive_square]

/-- The classical homogeneous finite-cylinder estimate for the full gradient.
The bottom contribution is the actual squared value on the bottom slice. -/
theorem full_gradient_cutoff_energy {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r a b ν L D : ℝ} (hla : l < a) (hab : a < b) (hbr : b < r)
    (hν : 0 < ν) (hD : 0 ≤ D)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {u ζ : Point n → ℝ}
    (hf : DGClassicalFields (O ×ˢ Ioo l r) A c (fun _ => 0) u)
    (hpde : ClassicalDivEq (O ×ˢ Ioo l r) A c (fun _ => 0) u)
    (hb : DGUniformBounds (O ×ˢ Ioo l r) A c (fun _ => 0) ν L D 0)
    (hu : ContinuousOn u (O ×ˢ Icc a b)) (hζ : DGSpatialCutoff O a b ζ) :
    Integrable (fun z => dgGradientSq (dgGradient u z) * (ζ z) ^ 2) (productVolume O (Ioo a b)) ∧
    ν * dgCylinderIntegral O a b (fun z => dgGradientSq (dgGradient u z) * (ζ z) ^ 2) ≤
      (2 + 8 * L ^ 2 / ν + 2 * D ^ 2 / ν) * dgCylinderIntegral O a b (cutoffValueError u ζ) +
        ∫ x in O, (u (x, a)) ^ 2 * (ζ (x, a)) ^ 2 := by
  have hp := cutoff_truncation_caccioppoli hO hla hab hbr.le hν hD (le_rfl : (0 : ℝ) ≤ 0)
    hf hpde hb hu hζ 1 0 (Or.inl rfl)
  have hm := cutoff_truncation_caccioppoli hO hla hab hbr.le hν hD (le_rfl : (0 : ℝ) ≤ 0)
    hf hpde hb hu hζ (-1) 0 (Or.inr rfl)
  have hsplit := cutoff_gradient_split_ae hO hla hbr hf.2.2.2 hζ
  have hsum : Integrable
      (fun z => dgTruncationEnergyDensity 1 0 u ζ z + dgTruncationEnergyDensity (-1) 0 u ζ z)
      (productVolume O (Ioo a b)) := hp.1.add hm.1
  have hfull : Integrable (fun z => dgGradientSq (dgGradient u z) * (ζ z) ^ 2)
      (productVolume O (Ioo a b)) := hsum.congr (Filter.EventuallyEq.symm hsplit)
  have hH : dgCylinderIntegral O a b (fun z => dgGradientSq (dgGradient u z) * (ζ z) ^ 2) =
      dgCylinderIntegral O a b (dgTruncationEnergyDensity 1 0 u ζ) +
        dgCylinderIntegral O a b (dgTruncationEnergyDensity (-1) 0 u ζ) := by
    unfold dgCylinderIntegral
    rw [integral_congr_ae hsplit, integral_add hp.1 hm.1]
  have hqp := dg_cutoff_quantities_integrable (σ := (1 : ℝ)) (k := (0 : ℝ)) hO hu hζ
  have hqm := dg_cutoff_quantities_integrable (σ := (-1 : ℝ)) (k := (0 : ℝ)) hO hu hζ
  have hX : dgCylinderIntegral O a b (dgTruncationCutoffError 1 0 u ζ) +
      dgCylinderIntegral O a b (dgTruncationCutoffError (-1) 0 u ζ) =
        dgCylinderIntegral O a b (cutoffValueError u ζ) := by
    unfold dgCylinderIntegral
    rw [← integral_add hqp.1 hqm.1]
    exact integral_congr_ae (.of_forall (signed_cutoff_error u ζ))
  have hS : dgSliceEnergy O (dgTruncation 1 0 u) ζ a +
      dgSliceEnergy O (dgTruncation (-1) 0 u) ζ a =
        ∫ x in O, (u (x, a)) ^ 2 * (ζ (x, a)) ^ 2 := by
    unfold dgSliceEnergy
    rw [← integral_add (hqp.2.2 a ⟨le_rfl, hab.le⟩) (hqm.2.2 a ⟨le_rfl, hab.le⟩)]
    exact integral_congr_ae (.of_forall (fun x => signed_slice_square u ζ (x, a)))
  refine ⟨hfull, ?_⟩
  rw [hH]
  have hh := add_le_add hp.2 hm.2
  simp only [mul_zero, zero_mul, add_zero] at hh
  rw [mul_add]
  calc
    _ ≤ (2 + 8 * L ^ 2 / ν + 2 * D ^ 2 / ν) *
          (dgCylinderIntegral O a b (dgTruncationCutoffError 1 0 u ζ) +
            dgCylinderIntegral O a b (dgTruncationCutoffError (-1) 0 u ζ)) +
          (dgSliceEnergy O (dgTruncation 1 0 u) ζ a + dgSliceEnergy O (dgTruncation (-1) 0 u) ζ a) := by
      linarith only [hh]
    _ = _ := by rw [hX, hS]

end Yau.F04Proof
