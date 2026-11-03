import Yau.Proofs.D06CircleSobolevCore

/-! The discrete ℓ²*ℓ¹ Young estimate, constructed as an actual Banach-space
sum of integer translation isometries. -/

open scoped lp

noncomputable section
namespace Yau.NodeProofs.D06Aux

abbrev CircleCoeffSpace := lp (fun _ : ℤ => ℂ) 2

def intShiftFn (j : ℤ) (a : CircleCoeffSpace) (n : ℤ) : ℂ := a (n - j)

theorem intShift_mem (j : ℤ) (a : CircleCoeffSpace) : Memℓp (intShiftFn j a) 2 := by
  apply memℓp_gen
  have h : Summable (fun n : ℤ => ‖a n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp a).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hs : Summable (fun n : ℤ => ‖a (n - j)‖ ^ 2) :=
    h.comp_injective (fun x y (hxy : x - j = y - j) => by omega)
  simpa only [intShiftFn, ENNReal.toReal_ofNat, Real.rpow_two] using hs

def intShift (j : ℤ) (a : CircleCoeffSpace) : CircleCoeffSpace :=
  ⟨intShiftFn j a, intShift_mem j a⟩

@[simp] theorem intShift_apply (j : ℤ) (a : CircleCoeffSpace) (n : ℤ) :
    intShift j a n = a (n - j) := rfl

theorem circleCoeffSpace_norm_sq (a : CircleCoeffSpace) :
    ‖a‖ ^ 2 = ∑' n : ℤ, ‖a n‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.hasSum_norm (p := 2) (by norm_num) a).tsum_eq.symm

theorem intShift_norm (j : ℤ) (a : CircleCoeffSpace) : ‖intShift j a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [circleCoeffSpace_norm_sq, circleCoeffSpace_norm_sq]
  have h := (Equiv.addRight (-j)).tsum_eq (fun n : ℤ => ‖a n‖ ^ 2)
  simpa only [intShift_apply, Equiv.coe_addRight, sub_eq_add_neg] using h

def intShiftLI (j : ℤ) : CircleCoeffSpace →ₗᵢ[ℂ] CircleCoeffSpace where
  toFun := intShift j
  map_add' a b := by ext n; rfl
  map_smul' c a := by ext n; rfl
  norm_map' := intShift_norm j

def l2Convolve (a : CircleCoeffSpace) (b : ℤ → ℂ) : CircleCoeffSpace :=
  ∑' j : ℤ, b j • intShift j a

theorem l2Convolve_series_summable (a : CircleCoeffSpace) (b : ℤ → ℂ)
    (hb : Summable (fun j : ℤ => ‖b j‖)) :
    Summable (fun j : ℤ => b j • intShift j a) := by
  apply Summable.of_norm
  simpa only [norm_smul, intShift_norm] using hb.mul_right ‖a‖

theorem l2Convolve_apply (a : CircleCoeffSpace) (b : ℤ → ℂ)
    (hb : Summable (fun j : ℤ => ‖b j‖)) (n : ℤ) :
    l2Convolve a b n = ∑' j : ℤ, b j * a (n - j) := by
  have hs := l2Convolve_series_summable a b hb
  calc
    _ = ∑' j : ℤ, (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n) (b j • intShift j a) :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).map_tsum hs
    _ = _ := tsum_congr (fun _ => rfl)

theorem l2Convolve_norm_le (a : CircleCoeffSpace) (b : ℤ → ℂ)
    (hb : Summable (fun j : ℤ => ‖b j‖)) :
    ‖l2Convolve a b‖ ≤ ‖a‖ * ∑' j : ℤ, ‖b j‖ := by
  have hs : Summable (fun j : ℤ => ‖b j • intShift j a‖) := by
    simpa only [norm_smul, intShift_norm] using hb.mul_right ‖a‖
  calc
    _ ≤ ∑' j : ℤ, ‖b j • intShift j a‖ := norm_tsum_le_tsum_norm hs
    _ = ‖a‖ * ∑' j : ℤ, ‖b j‖ := by
      simp only [norm_smul, intShift_norm, tsum_mul_right, mul_comm]

end Yau.NodeProofs.D06Aux
