import Yau.LeafProofs.L21QuantitativeWords

/-! Quantitative cutoff energy estimates for the actual smooth graph
equation, with constants independent of derivatives of its coefficients. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem norm_wirtRealCoefficient (t : Fin 2) : ‖wirtRealCoefficient t‖ = (1 / 2 : ℝ) := by
  fin_cases t <;> norm_num [wirtRealCoefficient]

theorem norm_wirtBarRealCoefficient (t : Fin 2) : ‖wirtBarRealCoefficient t‖ = (1 / 2 : ℝ) := by
  fin_cases t <;> norm_num [wirtBarRealCoefficient]

theorem norm_dbarRealCoefficient_le_one (A : X n → Matrix (Fin n) (Fin n) ℂ) (x : X n)
    (hA : ∀ i j, ‖A x i j‖ ≤ 1) (i : Fin n) (a : Yau.RIdx n) :
    ‖dbarRealCoefficient A i a x‖ ≤ 1 := by
  have hc : ‖if a.1 = i then wirtBarRealCoefficient a.2 else 0‖ ≤ (1 / 2 : ℝ) := by
    split_ifs
    · exact le_of_eq (norm_wirtBarRealCoefficient _)
    · norm_num
  calc
    _ ≤ ‖if a.1 = i then wirtBarRealCoefficient a.2 else 0‖ +
        ‖A x i a.1‖ * ‖wirtRealCoefficient a.2‖ := by
      simpa only [dbarRealCoefficient, norm_mul] using norm_add_le
        (if a.1 = i then wirtBarRealCoefficient a.2 else 0) (A x i a.1 * wirtRealCoefficient a.2)
    _ ≤ (1 / 2 : ℝ) + 1 * (1 / 2) := add_le_add hc
      (mul_le_mul (hA i a.1) (le_of_eq (norm_wirtRealCoefficient _)) (norm_nonneg _) (by norm_num))
    _ = 1 := by norm_num

theorem norm_dbarA_le_norm_fderiv (A : X n → Matrix (Fin n) (Fin n) ℂ) (f : X n → ℂ)
    (x : X n) (hA : ∀ i j, ‖A x i j‖ ≤ 1) (i : Fin n) :
    ‖dbarA A i f x‖ ≤ (realDimension n : ℝ) * ‖fderiv ℝ f x‖ := by
  rw [dbarA_eq_real_rows]
  calc
    _ ≤ ∑ a, ‖dbarRealCoefficient A i a x * fderiv ℝ f x (Yau.realVec a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Yau.RIdx n, ‖fderiv ℝ f x‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul]
      have hdf : ‖fderiv ℝ f x (Yau.realVec a)‖ ≤ ‖fderiv ℝ f x‖ := by
        simpa only [norm_realVec, mul_one] using (fderiv ℝ f x).le_opNorm (Yau.realVec a)
      exact (mul_le_mul (norm_dbarRealCoefficient_le_one A x hA i a) hdf
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, realDimension]

theorem norm_add_sq_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hh := (sq_le_sq₀ (norm_nonneg (a + b)) (by positivity : 0 ≤ ‖a‖ + ‖b‖)).mpr (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

def cutoffTest {O : Set (X n)} (χ : X n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O)
    (v : X n → ℂ) (hv : ContDiff ℝ ∞ v) : CompactTest O :=
  ⟨fun x => (χ x : ℂ) * v x, (Complex.ofRealCLM.contDiff.comp hχ).mul hv,
    (hcχ.comp_left Complex.ofReal_zero).mul_right,
    tsupport_mul_subset_left.trans ((tsupport_comp_subset Complex.ofReal_zero χ).trans hsχ)⟩

theorem cutoff_compact_gradient_energy {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (χ : X n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O)
    (v : X n → ℂ) (hv : ContDiff ℝ ∞ v) :
    (∑ a : Yau.RIdx n, ∫ x, ‖fderiv ℝ (fun y => (χ y : ℂ) * v y) x (Yau.realVec a)‖ ^ 2
      ∂Yau.lebesgueC n) ≤
        32 * ((∑ i : Fin n, ∫ x, ‖(χ x : ℂ) * dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n) +
          ∑ i : Fin n, ∫ x, ‖v x * dbarA A i (fun y => (χ y : ℂ)) x‖ ^ 2 ∂Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  let u := cutoffTest χ hχ hcχ hsχ v hv
  let χC := ofRealTest χ hχ hcχ hsχ
  have hχC : ContDiff ℝ ∞ (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hInt1 (i : Fin n) : Integrable (fun x => ‖(χ x : ℂ) * dbarA A i v x‖ ^ 2)
      (Yau.lebesgueC n) := by
    obtain ⟨hh, hc, _hs⟩ := Yau.LeafProofs.L14Aux.compact_complex_cutoff_properties
      hO χ hχ hcχ hsχ (dbarA A i v) (contDiffOn_dbarA hO hA i hv.contDiffOn)
    exact (hh.continuous.memLp_of_hasCompactSupport hc).integrable_norm_pow (p := 2) (by decide)
  have hInt2 (i : Fin n) : Integrable (fun x => ‖v x * dbarA A i (fun y => (χ y : ℂ)) x‖ ^ 2)
      (Yau.lebesgueC n) := by
    let g := testD hO hA i χC
    exact ((hv.mul g.property.1).continuous.memLp_of_hasCompactSupport g.property.2.1.mul_left).integrable_norm_pow
      (p := 2) (by decide)
  have hD (i : Fin n) (x : X n) : dbarA A i u x =
      (χ x : ℂ) * dbarA A i v x + v x * dbarA A i (fun y => (χ y : ℂ)) x :=
    dbarA_mul A i (hχC.differentiable (by simp) x) (hv.differentiable (by simp) x)
  have hi (i : Fin n) : (∫ x, ‖dbarA A i u x‖ ^ 2 ∂Yau.lebesgueC n) ≤
      2 * (∫ x, ‖(χ x : ℂ) * dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n) +
        2 * (∫ x, ‖v x * dbarA A i (fun y => (χ y : ℂ)) x‖ ^ 2 ∂Yau.lebesgueC n) := by
    have hBoth : Integrable (fun x => 2 * ‖(χ x : ℂ) * dbarA A i v x‖ ^ 2 +
        2 * ‖v x * dbarA A i (fun y => (χ y : ℂ)) x‖ ^ 2) (Yau.lebesgueC n) :=
      ((hInt1 i).const_mul 2).add ((hInt2 i).const_mul 2)
    have hh := integral_mono (integrable_dbarA_norm_sq hO hA u i)
      hBoth
      (fun x => by rw [hD]; exact norm_add_sq_le_two _ _)
    rw [integral_add ((hInt1 i).const_mul 2) ((hInt2 i).const_mul 2),
      integral_const_mul, integral_const_mul] at hh
    exact hh
  calc
    _ ≤ 16 * ∑ i : Fin n, ∫ x, ‖dbarA A i u x‖ ^ 2 ∂Yau.lebesgueC n :=
      first_order_energy_on_compact_tests hO hA hsmall u
    _ ≤ 16 * ∑ i : Fin n,
        (2 * (∫ x, ‖(χ x : ℂ) * dbarA A i v x‖ ^ 2 ∂Yau.lebesgueC n) +
          2 * (∫ x, ‖v x * dbarA A i (fun y => (χ y : ℂ)) x‖ ^ 2 ∂Yau.lebesgueC n)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) (by norm_num)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

end Yau.LeafProofs.L21Aux
