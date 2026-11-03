import Yau.Proofs.F04Caccioppoli

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem bottom_cylinder_restrict {n : ℕ} {O : Set (Space n)} {a b δ : ℝ}
    (hδ : a ≤ δ) :
    (productVolume O (Ioo a b)).restrict {z : Point n | δ < z.2} =
      productVolume O (Ioo δ b) := by
  rw [dg_productVolume_eq_restrict, Measure.restrict_restrict
    (isOpen_lt continuous_const continuous_snd).measurableSet, dg_productVolume_eq_restrict]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
  constructor
  · rintro ⟨hδz, hzO, _haz, hzb⟩
    exact ⟨hzO, hδz, hzb⟩
  · rintro ⟨hzO, hδz, hzb⟩
    exact ⟨hδz, hzO, hδ.trans_lt hδz, hzb⟩

/-- Establish the actual integral before passing the bottom time to zero.
The explicit quadratic bottom error then vanishes in that limit. -/
theorem bottom_time_integral_bound {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {s B D : ℝ} (hs : 0 < s) (hB : 0 ≤ B) (hD : 0 ≤ D) {H : Point n → ℝ}
    (_hm : AEStronglyMeasurable H (productVolume O (Ioo 0 s)))
    (hn : ∀ᵐ z ∂productVolume O (Ioo 0 s), 0 ≤ H z)
    (hp : ∀ δ ∈ Ioo 0 s, Integrable H (productVolume O (Ioo δ s)) ∧
      dgCylinderIntegral O δ s H ≤ B + D * δ ^ 2) :
    Integrable H (productVolume O (Ioo 0 s)) ∧ dgCylinderIntegral O 0 s H ≤ B := by
  let μ := productVolume O (Ioo 0 s)
  let U : ℝ → Set (Point n) := fun δ => if δ ∈ Ioo 0 s then {z | δ < z.2} else ∅
  have hUmeas (δ : ℝ) : MeasurableSet (U δ) := by
    dsimp only [U]
    split_ifs
    · exact (isOpen_lt continuous_const continuous_snd).measurableSet
    · exact MeasurableSet.empty
  have hcover : AECover μ (𝓝[>] (0 : ℝ)) U := by
    refine ⟨?_, hUmeas⟩
    have hmem : ∀ᵐ z ∂μ, z ∈ O ×ˢ Ioo 0 s := by
      rw [show μ = volume.restrict (O ×ˢ Ioo 0 s) from dg_productVolume_eq_restrict O _]
      exact ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet
    filter_upwards [hmem] with z hz
    filter_upwards [Ioo_mem_nhdsGT hs,
      (eventually_lt_nhds hz.2.1).filter_mono nhdsWithin_le_nhds] with δ hδ hδz
    simp only [U, ite_eq_left hδ, mem_ofPred_eq]
    exact hδz
  have hrestrict (δ : ℝ) (hδ : δ ∈ Ioo 0 s) :
      μ.restrict (U δ) = productVolume O (Ioo δ s) := by
    rw [show U δ = {z : Point n | δ < z.2} from ite_eq_left hδ]
    exact bottom_cylinder_restrict hδ.1.le
  have hfi (δ : ℝ) : IntegrableOn H (U δ) μ := by
    by_cases hδ : δ ∈ Ioo 0 s
    · rw [IntegrableOn, hrestrict δ hδ]
      exact (hp δ hδ).1
    · simp only [U, ite_eq_right hδ, integrableOn_empty]
  have hbound : ∀ δ, (∫ z in U δ, H z ∂μ) ≤ B + D * s ^ 2 := by
    intro δ
    by_cases hδ : δ ∈ Ioo 0 s
    · rw [hrestrict δ hδ]
      have hh := (hp δ hδ).2
      change (∫ z, H z ∂productVolume O (Ioo δ s)) ≤ B + D * δ ^ 2 at hh
      have hsq : δ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hδ.1.le hδ.2.le 2
      linarith only [hh, mul_le_mul_of_nonneg_left hsq hD]
    · simp only [U, ite_eq_right hδ, setIntegral_empty]
      positivity
  have hInt : Integrable H μ := hcover.integrable_of_integral_bounded_of_nonneg_ae
    (B + D * s ^ 2) hfi hn (.of_forall hbound)
  refine ⟨hInt, ?_⟩
  have herr : Tendsto (fun δ : ℝ => D * δ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hh := ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).pow 2).const_mul D
    have hh' : Tendsto (fun δ : ℝ => D * δ ^ 2) (𝓝 0) (𝓝 0) := by
      convert hh using 1 <;> simp only [id_eq, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    exact hh'.mono_left nhdsWithin_le_nhds
  have hlim := (hcover.integral_tendsto_of_countably_generated hInt).sub herr
  have hle : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ z in U δ, H z ∂μ) - D * δ ^ 2 ≤ B := by
    filter_upwards [Ioo_mem_nhdsGT hs] with δ hδ
    rw [hrestrict δ hδ]
    have hh := (hp δ hδ).2
    change (∫ z, H z ∂productVolume O (Ioo δ s)) ≤ B + D * δ ^ 2 at hh
    linarith only [hh]
  have hh := le_of_tendsto hlim hle
  rw [sub_zero] at hh
  convert hh using 1
  rfl

end Yau.F04Proof
