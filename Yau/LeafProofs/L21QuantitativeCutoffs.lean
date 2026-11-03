import Yau.LeafProofs.L21QuantitativeEnergy

/-! Fixed smooth cutoffs have uniform directional constants, and actual
compact multipliers preserve the precise local squared-integral bounds. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem exists_cutoff_directional_bound {χ : X n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x (a : Yau.RIdx n), ‖fderiv ℝ χ x (Yau.realVec a)‖ ≤ L := by
  obtain ⟨C, hC⟩ := (hcχ.fderiv ℝ).exists_bound_of_continuous (hχ.continuous_fderiv (by simp))
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro x a
  have hh : ‖fderiv ℝ χ x (Yau.realVec a)‖ ≤ ‖fderiv ℝ χ x‖ := by
    simpa only [norm_realVec, mul_one] using (fderiv ℝ χ x).le_opNorm (Yau.realVec a)
  exact hh.trans ((hC x).trans (by linarith [le_max_left C 0]))

theorem norm_dbarA_ofReal_le_directional_bound
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (x : X n)
    (hA : ∀ i j, ‖A x i j‖ ≤ 1) {χ : X n → ℝ} (hχ : DifferentiableAt ℝ χ x)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ a : Yau.RIdx n, ‖fderiv ℝ χ x (Yau.realVec a)‖ ≤ L)
    (i : Fin n) : ‖dbarA A i (fun y => (χ y : ℂ)) x‖ ≤ (realDimension n : ℝ) * L := by
  rw [dbarA_eq_real_rows]
  calc
    _ ≤ ∑ a, ‖dbarRealCoefficient A i a x * fderiv ℝ (fun y => (χ y : ℂ)) x (Yau.realVec a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Yau.RIdx n, L := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, fderiv_ofReal_apply hχ, Complex.norm_real]
      exact (mul_le_mul (norm_dbarRealCoefficient_le_one A x hA i a) (hb a)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul L)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, realDimension]

theorem integral_compact_multiplier_norm_sq_le {O : Set (X n)}
    (b f : X n → ℂ) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖b x‖ ≤ C)
    (hs : tsupport b ⊆ O)
    (hProd : Integrable (fun x => ‖b x * f x‖ ^ 2) (Yau.lebesgueC n))
    (hF : Integrable (fun x => ‖f x‖ ^ 2) ((Yau.lebesgueC n).restrict O)) :
    (∫ x, ‖b x * f x‖ ^ 2 ∂Yau.lebesgueC n) ≤
      C ^ 2 * ∫ x in O, ‖f x‖ ^ 2 ∂Yau.lebesgueC n := by
  have he : (∫ x in O, ‖b x * f x‖ ^ 2 ∂Yau.lebesgueC n) =
      ∫ x, ‖b x * f x‖ ^ 2 ∂Yau.lebesgueC n :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hn : x ∉ tsupport b := fun hh => hx (hs hh)
      simp only [image_eq_zero_of_notMem_tsupport hn, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)])
  rw [← he, ← integral_const_mul]
  apply integral_mono hProd.restrict (hF.const_mul _)
  intro x
  change ‖b x * f x‖ ^ 2 ≤ C ^ 2 * ‖f x‖ ^ 2
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hb x)) (sq_nonneg _)

theorem dbarA_ofReal_cutoff_bound {O : Set (X n)}
    (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ x ∈ O, ∀ i j, ‖A x i j‖ ≤ 1)
    {χ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ O)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ x (a : Yau.RIdx n), ‖fderiv ℝ χ x (Yau.realVec a)‖ ≤ L)
    (i : Fin n) (x : X n) :
    ‖dbarA A i (fun y => (χ y : ℂ)) x‖ ≤ (realDimension n : ℝ) * L := by
  by_cases hx : x ∈ O
  · exact norm_dbarA_ofReal_le_directional_bound A x (hA x hx)
      (hχ.differentiable (by simp) x) hL (hb x) i
  · have hn : x ∉ tsupport χ := fun hh => hx (hsχ hh)
    have hnC : x ∉ tsupport (fun y => (χ y : ℂ)) := fun hh =>
      hn ((tsupport_comp_subset Complex.ofReal_zero χ) hh)
    have hd := fderiv_of_notMem_tsupport ℝ hnC
    simp only [dbarA, Yau.wirtBar, Yau.wirt, hd, _root_.zero_apply, mul_zero,
      zero_add, sub_zero, Finset.sum_const_zero, norm_zero]
    positivity

end Yau.LeafProofs.L21Aux
