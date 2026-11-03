import Yau.Proofs.D06BoundaryEnergySym

/-! The original two translation differences obey the source's sharp averaged
bounds before the first W¹ estimate, with the fixed pair of Hardy traces. -/

open scoped ComplexOrder Matrix
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

theorem hardyRelativeTrace_energy_integrable (θ : HardyCircle) :
    Integrable (fun t => frobSq (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t - 1))
      hardyCircleMeasure := matrix_frobSq_integrable _ (fun i j =>
    (matrix_entries_memLp_sub_one _
      (hardyRelativeTrace_memLp L hLp hHerm m hm hLower M hM hUpper θ) i j).mono_exponent le_top)

theorem hardyQTrace_difference_energy (θ : HardyCircle) :
    circleDifference (hardyQTrace L hLp hHerm m hm hLower M hM hUpper) θ ≤
      M * hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper θ := by
  let Q := hardyQTrace L hLp hHerm m hm hLower M hM hUpper
  let P := hardyPTrace L hLp hHerm m hm hLower M hM hUpper
  have hQ := hardyQTrace_memLp L hLp hHerm m hm hLower M hM hUpper
  have hD : Integrable (fun t => frobSq (Q (t + θ) - Q t)) hardyCircleMeasure :=
    matrix_frobSq_integrable _ (fun i j => (((hQ i j).comp_measurePreserving
      (measurePreserving_add_right hardyCircleMeasure θ)).sub (hQ i j)).mono_exponent le_top)
  have hE := hardyRelativeTrace_energy_integrable L hLp hHerm m hm hLower M hM hUpper θ
  have hpoint : (fun t => frobSq (Q (t + θ) - Q t)) ≤ᵐ[hardyCircleMeasure]
      fun t => M * frobSq (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t - 1) := by
    filter_upwards [hardyPTrace_inverse L hLp hHerm m hm hLower M hM hUpper,
      hardyQTrace_bound L hLp hHerm m hm hLower M hM hUpper] with t hi hb
    have hs : matOpNormR (Q t) ^ 2 ≤ M := by
      have hsq := Real.sq_sqrt hM
      nlinarith [matOpNormR_nonneg (Q t), Real.sqrt_nonneg M]
    have hd := factor_difference_bound (Q t) (Q (t + θ)) (P t) hi.1
    change frobSq (Q (t + θ) - Q t) ≤ M * frobSq (Q (t + θ) * P t - 1)
    exact hd.trans (by nlinarith [frobSq_nonneg (Q (t + θ) * P t - 1)])
  calc
    _ ≤ ∫ t, M * frobSq (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t - 1)
        ∂hardyCircleMeasure := integral_mono_ae hD (hE.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

theorem hardyPTrace_difference_energy (θ : HardyCircle) :
    circleDifference (hardyPTrace L hLp hHerm m hm hLower M hM hUpper) θ ≤
      m⁻¹ * hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper θ := by
  let Q := hardyQTrace L hLp hHerm m hm hLower M hM hUpper
  let P := hardyPTrace L hLp hHerm m hm hLower M hM hUpper
  have hP := hardyPTrace_memLp L hLp hHerm m hm hLower M hM hUpper
  have hD : Integrable (fun t => frobSq (P (t + θ) - P t)) hardyCircleMeasure :=
    matrix_frobSq_integrable _ (fun i j => (((hP i j).comp_measurePreserving
      (measurePreserving_add_right hardyCircleMeasure θ)).sub (hP i j)).mono_exponent le_top)
  have hE := hardyRelativeTrace_energy_integrable L hLp hHerm m hm hLower M hM hUpper θ
  have hiθ := (measurePreserving_add_right hardyCircleMeasure θ).quasiMeasurePreserving.ae
    (hardyPTrace_inverse L hLp hHerm m hm hLower M hM hUpper)
  have hbθ := (measurePreserving_add_right hardyCircleMeasure θ).quasiMeasurePreserving.ae
    (hardyPTrace_bound L hLp hHerm m hm hLower M hM hUpper)
  have hpoint : (fun t => frobSq (P (t + θ) - P t)) ≤ᵐ[hardyCircleMeasure]
      fun t => m⁻¹ * frobSq (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t - 1) := by
    filter_upwards [hiθ, hbθ] with t hi hb
    have hs : matOpNormR (P (t + θ)) ^ 2 ≤ m⁻¹ := by
      have hsq := (sq_le_sq₀ (matOpNormR_nonneg (P (t + θ)))
        (inv_nonneg.mpr (Real.sqrt_nonneg m))).mpr hb
      simpa only [inv_pow, Real.sq_sqrt hm.le] using hsq
    have hd := inverse_difference_bound (Q (t + θ)) (P t) (P (t + θ)) hi.1
    change frobSq (P (t + θ) - P t) ≤ m⁻¹ * frobSq (Q (t + θ) * P t - 1)
    exact hd.trans (mul_le_mul_of_nonneg_right hs (frobSq_nonneg _))
  calc
    _ ≤ ∫ t, m⁻¹ * frobSq (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t - 1)
        ∂hardyCircleMeasure := integral_mono_ae hD (hE.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

theorem hardyQTrace_difference_sharp (θ : HardyCircle) :
    circleDifference (hardyQTrace L hLp hHerm m hm hLower M hM hUpper) θ ≤
      M / (2 * m ^ 2) * circleDifference L θ := by
  have h := circleDifference_sharp_of_symmetric_energy _ L
    (hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper) M (m ^ 2)⁻¹ hM
    (hardyQTrace_difference_energy L hLp hHerm m hm hLower M hM hUpper)
    (hardyTranslationEnergy_symmetric L hLp hHerm m hm hLower M hM hUpper) θ
  convert h using 1 <;> field_simp <;> ring

theorem hardyPTrace_difference_sharp (θ : HardyCircle) :
    circleDifference (hardyPTrace L hLp hHerm m hm hLower M hM hUpper) θ ≤
      1 / (2 * m ^ 3) * circleDifference L θ := by
  have h := circleDifference_sharp_of_symmetric_energy _ L
    (hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper) m⁻¹ (m ^ 2)⁻¹ (inv_nonneg.mpr hm.le)
    (hardyPTrace_difference_energy L hLp hHerm m hm hLower M hM hUpper)
    (hardyTranslationEnergy_symmetric L hLp hHerm m hm hLower M hM hUpper) θ
  convert h using 1 <;> field_simp <;> ring

end Yau.NodeProofs.D06Aux
