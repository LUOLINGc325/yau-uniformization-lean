import Yau.Proofs.F04Caccioppoli

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem smooth_local_directional_ibp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U)
    {u φ : E → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (e : E) :
    (∫ x in U, u x * fderiv ℝ φ x e ∂μ) =
      -(∫ x in U, fderiv ℝ u x e * φ x ∂μ) := by
  obtain ⟨w, hw, hcw, hwu⟩ := dg_smooth_compact_extension hU hcφ hφU hu
  have hwd : Continuous (fun x => fderiv ℝ w x e) :=
    (hw.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφd : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hInt1 : Integrable (fun x => fderiv ℝ w x e * φ x) μ :=
    (hwd.mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left
  have hInt2 : Integrable (fun x => w x * fderiv ℝ φ x e) μ :=
    (hw.continuous.mul hφd).integrable_of_hasCompactSupport hcw.mul_right
  have hInt3 : Integrable (fun x => w x * φ x) μ :=
    (hw.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hcw.mul_right
  have hglobal := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hInt1 hInt2 hInt3
    (fun _ _ => hw.differentiable (by simp) _) (fun _ _ => hφ.differentiable (by simp) _)
  have hleft : (∫ x, w x * fderiv ℝ φ x e ∂μ) =
      ∫ x in U, u x * fderiv ℝ φ x e ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport φ
      · rw [(hwu x hx).eq_of_nhds]
      · rw [fderiv_of_notMem_tsupport ℝ hx]
        simp only [zero_apply, mul_zero]
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hφU h))]
      simp only [zero_apply, mul_zero]
  have hright : (∫ x, fderiv ℝ w x e * φ x ∂μ) =
      ∫ x in U, fderiv ℝ u x e * φ x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport φ
      · rw [(hwu x hx).fderiv_eq]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp only [mul_zero]
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))]
      simp only [mul_zero]
  rw [hleft, hright] at hglobal
  exact hglobal

theorem classical_weakGradient {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    (hQ : IsOpen (O ×ˢ I)) {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) :
    WeakGradient O I u (dgGradient u) := by
  intro φ hφ i
  have : (volume : Measure (Point n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hh := smooth_local_directional_ibp (μ := (volume : Measure (Point n)))
    hQ hu hφ.1 hφ.2.1 hφ.2.2 (Yau.realVec i, 0)
  rw [dg_productVolume_eq_restrict]
  convert hh using 1
  · apply setIntegral_congr_fun hQ.measurableSet
    intro p _
    change u p * dgGradient φ p i = u p * fderiv ℝ φ p (Yau.realVec i, 0)
    rw [dgGradient_eq_joint_fderiv (hφ.1.differentiable (by simp) p) i]
  · congr 1
    apply setIntegral_congr_fun hQ.measurableSet
    intro p hp
    change dgGradient u p i * φ p = fderiv ℝ u p (Yau.realVec i, 0) * φ p
    rw [dgGradient_eq_joint_fderiv ((hu.contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp)) i]

end Yau.F04Proof
