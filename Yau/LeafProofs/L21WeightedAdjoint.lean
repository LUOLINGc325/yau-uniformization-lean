import Yau.LeafProofs.L21OperatorRows
import Yau.LeafProofs.L14

/-! Weighted formal adjoints in the original Euclidean coordinates. Only
the Euclidean compact-test integration lemmas from L14 are used here. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem integrable_local_mul_compact_derivative
    {O : Set (X n)} (hO : IsOpen O) {a u : X n → ℂ}
    (ha : ContinuousOn a O) (hu : ContDiff ℝ 1 u)
    (hcu : HasCompactSupport u) (hsu : tsupport u ⊆ O) (v : X n) :
    Integrable (fun x => a x * fderiv ℝ u x v) (Yau.lebesgueC n) := by
  have hd : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs : tsupport (fun x => fderiv ℝ u x v) ⊆ O :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsu
  simpa only [mul_comm] using Yau.LeafProofs.L14Aux.integrable_compactTest_mul_complex
    hO hd (hcu.fderiv_apply ℝ v) hs ha

theorem integral_local_mul_compact_fderiv
    {O : Set (X n)} (hO : IsOpen O) {a u : X n → ℂ}
    (ha : ContDiffOn ℝ 1 a O) (hu : ContDiff ℝ 1 u)
    (hcu : HasCompactSupport u) (hsu : tsupport u ⊆ O) (v : X n) :
    (∫ x, a x * fderiv ℝ u x v ∂Yau.lebesgueC n) =
      -(∫ x, fderiv ℝ a x v * u x ∂Yau.lebesgueC n) := by
  letI : (Yau.lebesgueC n).IsAddHaarMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  have hda : ContinuousOn (fun x => fderiv ℝ a x v) O :=
    (ha.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  have hintda : Integrable (fun x => fderiv ℝ a x v * u x) (Yau.lebesgueC n) := by
    simpa only [mul_comm] using Yau.LeafProofs.L14Aux.integrable_compactTest_mul_complex
      hO hu.continuous hcu hsu hda
  have hintau : Integrable (fun x => a x * u x) (Yau.lebesgueC n) := by
    simpa only [mul_comm] using Yau.LeafProofs.L14Aux.integrable_compactTest_mul_complex
      hO hu.continuous hcu hsu ha.continuousOn
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hintda
    (integrable_local_mul_compact_derivative hO ha.continuousOn hu hcu hsu v) hintau
    (fun x hx => (ha.contDiffAt (hO.mem_nhds (hsu hx))).differentiableAt one_ne_zero)
    (fun x _ => hu.differentiable one_ne_zero x)

def weightDensity (φ : X n → ℝ) (x : X n) : ℂ := Real.exp (-φ x)

theorem weightDensity_ne_zero (φ : X n → ℝ) (x : X n) : weightDensity φ x ≠ 0 := by
  change (Real.exp (-φ x) : ℂ) ≠ 0
  exact_mod_cast Real.exp_ne_zero (-φ x)

/-- The divergence expression uses the actual reciprocal density and actual
real derivatives, so it is meaningful independently of any adjoint claim. -/
def weightedDStarDiv (A : X n → Matrix (Fin n) (Fin n) ℂ) (φ : X n → ℝ)
    (i : Fin n) (v : X n → ℂ) (x : X n) : ℂ :=
  star (-(weightDensity φ x)⁻¹ * ∑ a : Yau.RIdx n,
    fderiv ℝ (fun y => star (v y) * dbarRealCoefficient A i a y * weightDensity φ y)
      x (Yau.realVec a))

theorem weightedDStarDiv_pairing_pointwise
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (φ : X n → ℝ)
    (i : Fin n) (u v : X n → ℂ) (x : X n) :
    star (weightedDStarDiv A φ i v x) * u x * weightDensity φ x =
      -(∑ a : Yau.RIdx n,
        fderiv ℝ (fun y => star (v y) * dbarRealCoefficient A i a y * weightDensity φ y)
          x (Yau.realVec a) * u x) := by
  simp only [weightedDStarDiv, star_star, ← Finset.sum_mul]
  field_simp [weightDensity_ne_zero φ x]

/-- Genuine compact-test Green identity for the weighted graph operator. -/
theorem integral_weighted_dbarA_green
    {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    {u v : X n → ℂ} (hu : ContDiff ℝ ∞ u) (hv : ContDiffOn ℝ ∞ v O)
    (hcu : HasCompactSupport u) (hsu : tsupport u ⊆ O) (i : Fin n) :
    (∫ x, star (v x) * dbarA A i u x * weightDensity φ x ∂Yau.lebesgueC n) =
      ∫ x, star (weightedDStarDiv A φ i v x) * u x * weightDensity φ x ∂Yau.lebesgueC n := by
  let κ : Yau.RIdx n → X n → ℂ := fun a x =>
    star (v x) * dbarRealCoefficient A i a x * weightDensity φ x
  have hκ (a : Yau.RIdx n) : ContDiffOn ℝ ∞ (κ a) O :=
    (((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hv).mul
      (dbarRealCoefficient_smoothOn hA i a)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn hφ.neg))
  have hκdu (a : Yau.RIdx n) :
      Integrable (fun x => κ a x * fderiv ℝ u x (Yau.realVec a)) (Yau.lebesgueC n) :=
    integrable_local_mul_compact_derivative hO (hκ a).continuousOn
      (hu.of_le (by simp)) hcu hsu _
  have hdκu (a : Yau.RIdx n) :
      Integrable (fun x => fderiv ℝ (κ a) x (Yau.realVec a) * u x) (Yau.lebesgueC n) := by
    have hdκ : ContinuousOn (fun x => fderiv ℝ (κ a) x (Yau.realVec a)) O :=
      ((hκ a).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
    simpa only [mul_comm] using Yau.LeafProofs.L14Aux.integrable_compactTest_mul_complex
      hO hu.continuous hcu hsu hdκ
  calc
    _ = ∫ x, ∑ a : Yau.RIdx n, κ a x * fderiv ℝ u x (Yau.realVec a) ∂Yau.lebesgueC n := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [dbarA_eq_real_rows, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [κ]
      ring
    _ = ∑ a : Yau.RIdx n, ∫ x, κ a x * fderiv ℝ u x (Yau.realVec a) ∂Yau.lebesgueC n :=
      integral_finset_sum _ (fun a _ => hκdu a)
    _ = ∑ a : Yau.RIdx n, -(∫ x, fderiv ℝ (κ a) x (Yau.realVec a) * u x ∂Yau.lebesgueC n) := by
      apply Finset.sum_congr rfl
      intro a _
      exact integral_local_mul_compact_fderiv hO ((hκ a).of_le (by simp))
        (hu.of_le (by simp)) hcu hsu _
    _ = -(∫ x, ∑ a : Yau.RIdx n, fderiv ℝ (κ a) x (Yau.realVec a) * u x ∂Yau.lebesgueC n) := by
      rw [integral_finset_sum _ (fun a _ => hdκu a), Finset.sum_neg_distrib]
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (weightedDStarDiv_pairing_pointwise A φ i u v x).symm

end Yau.LeafProofs.L21Aux
