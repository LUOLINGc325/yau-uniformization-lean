import Yau.Proofs.V03PositiveFourier
import Yau.Proofs.V03FourierConjugate

/-! The real part of the genuine positive Fourier projection reconstructs
the original real trace, with its original zero mode retained. -/

open scoped Topology ComplexConjugate
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem fourierCoeff_real_zero_im (q : AddCircle T → ℝ) :
    (fourierCoeff (fun x => (q x : ℂ)) 0).im = 0 := by
  have hh := congrArg Complex.im (fourierCoeff_real_neg q 0)
  simp only [neg_zero, Complex.conj_im] at hh
  linarith

theorem real_positiveFourier_reconstruction {q : AddCircle T → ℝ} (hq : Continuous q)
    (hcoeff : Summable (fourierCoeff (fun x => (q x : ℂ)))) (x : AddCircle T) :
    2 * (positiveFourierSum (fun n : ℕ => fourierCoeff (fun y => (q y : ℂ)) (n : ℤ)) x).re -
      (fourierCoeff (fun y => (q y : ℂ)) 0).re = q x := by
  let b : ℕ → ℂ := fun n => fourierCoeff (fun y => (q y : ℂ)) (n : ℤ)
  let F : ℤ → ℂ := fun k => fourierCoeff (fun y => (q y : ℂ)) k * fourier k x
  have hb : Summable b := hcoeff.comp_injective Nat.cast_injective
  have hF : Summable F := by
    apply Summable.of_norm_bounded hcoeff.norm
    intro k
    simp only [F, norm_mul, fourier_point_norm, mul_one]
    exact le_rfl
  have hn : Summable (fun n : ℕ => F (n : ℤ)) := hF.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => F (-((n + 1 : ℕ) : ℤ))) :=
    hF.comp_injective (fun n m h => by omega)
  have hP : positiveFourierSum b x = ∑' n : ℕ, F (n : ℤ) := by
    rw [positiveFourierSum_apply hb]
    simp only [b, F, fourier_nat_pow]
  have htail : (∑' n : ℕ, F ((n + 1 : ℕ) : ℤ)) = positiveFourierSum b x - F 0 := by
    rw [hP, hn.tsum_eq_zero_add]
    ring
  have hnegFun : (fun n : ℕ => F (-((n + 1 : ℕ) : ℤ))) =
      fun n => conj (F ((n + 1 : ℕ) : ℤ)) := by
    funext n
    simp only [F, fourierCoeff_real_neg, fourier_neg, map_mul]
  simp only [Nat.cast_add, Nat.cast_one] at hnegFun htail
  let f : C(AddCircle T, ℂ) := ⟨fun y => (q y : ℂ), Complex.continuous_ofReal.comp hq⟩
  have hfcoe : (f : AddCircle T → ℂ) = fun y => (q y : ℂ) := rfl
  have hcf : Summable (fourierCoeff f) := by simpa only [hfcoe] using hcoeff
  have hr : (∑' k : ℤ, F k) = (q x : ℂ) := by
    simpa only [F, hfcoe, smul_eq_mul] using
      (has_pointwise_sum_fourier_series_of_summable hcf x).tsum_eq
  have heq : (q x : ℂ) = positiveFourierSum b x + conj (positiveFourierSum b x - F 0) := by
    rw [← hr, tsum_of_nat_of_neg_add_one hn hneg, ← hP, hnegFun, ← Complex.conj_tsum, htail]
  have hre := congrArg Complex.re heq
  simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re, Complex.sub_re,
    F, fourier_zero, mul_one] at hre
  dsimp only [b] at hre
  linarith

end Yau.Blueprint.V03Proof
