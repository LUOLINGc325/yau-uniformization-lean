import Yau.Proofs.V03PositiveFourier
import Yau.Proofs.V03FourierImaginary
import Yau.Proofs.V03RealPositiveFourier
import Yau.Proofs.V03GagliardoCircle

/-! The actual positive Fourier projection defines a continuous harmonic
conjugate trace. Its original weighted Fourier energy is preserved exactly. -/

open scoped Topology ComplexConjugate
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

def analyticCircleProjection (q : AddCircle T → ℝ) : C(AddCircle T, ℂ) :=
  (2 : ℂ) • positiveFourierSum (fun n : ℕ => fourierCoeff (fun x => (q x : ℂ)) (n : ℤ)) -
    ContinuousMap.const _ (fourierCoeff (fun x => (q x : ℂ)) 0)

def harmonicConjugateCircle (q : AddCircle T → ℝ) : C(AddCircle T, ℝ) :=
  ⟨fun x => (analyticCircleProjection q x).im,
    Complex.continuous_im.comp (analyticCircleProjection q).continuous⟩

theorem analyticCircleProjection_coeff (q : AddCircle T → ℝ) (k : ℤ) :
    fourierCoeff (analyticCircleProjection q) k =
      2 * fourierCoeff (positiveFourierSum (T := T)
        (fun n : ℕ => fourierCoeff (fun x => (q x : ℂ)) (n : ℤ))) k -
        (if k = 0 then fourierCoeff (fun x => (q x : ℂ)) 0 else 0) := by
  change fourierCoeffFunctional k ((2 : ℂ) • _ - _) = _
  rw [map_sub, map_smul, fourierCoeffFunctional_apply, fourierCoeffFunctional_apply]
  simp only [smul_eq_mul]
  change _ - fourierCoeff (fun _ : AddCircle T =>
    fourierCoeff (fun x : AddCircle T => (q x : ℂ)) 0) k = _
  rw [fourierCoeff_const_value]

theorem analyticCircleProjection_coeff_nat {q : AddCircle T → ℝ}
    (hb : Summable (fun n : ℕ => fourierCoeff (fun x => (q x : ℂ)) (n : ℤ))) (m : ℕ) :
    fourierCoeff (analyticCircleProjection q) (m : ℤ) =
      if m = 0 then fourierCoeff (fun x => (q x : ℂ)) 0
      else 2 * fourierCoeff (fun x => (q x : ℂ)) (m : ℤ) := by
  rw [analyticCircleProjection_coeff, positiveFourierSum_coeff_nat hb]
  by_cases hm : m = 0
  · subst m; simp; ring
  · simp [hm]

theorem analyticCircleProjection_coeff_negSucc {q : AddCircle T → ℝ}
    (hb : Summable (fun n : ℕ => fourierCoeff (fun x => (q x : ℂ)) (n : ℤ))) (m : ℕ) :
    fourierCoeff (analyticCircleProjection q) (-((m + 1 : ℕ) : ℤ)) = 0 := by
  rw [analyticCircleProjection_coeff, positiveFourierSum_coeff_negSucc hb]
  have hne : -((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
  rw [if_neg hne]
  ring

theorem harmonicConjugateCircle_coeff_pos_norm {q : AddCircle T → ℝ}
    (hb : Summable (fun n : ℕ => fourierCoeff (fun x => (q x : ℂ)) (n : ℤ))) (m : ℕ) :
    ‖fourierCoeff (fun x => (harmonicConjugateCircle q x : ℂ)) ((m + 1 : ℕ) : ℤ)‖ =
      ‖fourierCoeff (fun x => (q x : ℂ)) ((m + 1 : ℕ) : ℤ)‖ := by
  change ‖fourierCoeff (fun x => ((analyticCircleProjection q x).im : ℂ)) _‖ = _
  rw [fourierCoeff_imaginary, analyticCircleProjection_coeff_nat hb,
    analyticCircleProjection_coeff_negSucc hb]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    map_zero, sub_zero, norm_div, norm_mul, Complex.norm_I, mul_one]
  norm_num

theorem harmonicConjugateCircle_coeff_neg_norm {q : AddCircle T → ℝ}
    (hb : Summable (fun n : ℕ => fourierCoeff (fun x => (q x : ℂ)) (n : ℤ))) (m : ℕ) :
    ‖fourierCoeff (fun x => (harmonicConjugateCircle q x : ℂ)) (-((m + 1 : ℕ) : ℤ))‖ =
      ‖fourierCoeff (fun x => (q x : ℂ)) (-((m + 1 : ℕ) : ℤ))‖ := by
  change ‖fourierCoeff (fun x => ((analyticCircleProjection q x).im : ℂ)) _‖ = _
  rw [fourierCoeff_imaginary, analyticCircleProjection_coeff_negSucc hb,
    neg_neg, analyticCircleProjection_coeff_nat hb, fourierCoeff_real_neg]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    zero_sub, norm_neg, norm_div, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_conj]
  norm_num

theorem harmonicConjugateCircle_dirichlet {q : AddCircle T → ℝ}
    (hb : Summable (fun n : ℕ => fourierCoeff (fun x => (q x : ℂ)) (n : ℤ))) :
    circleDirichlet (fun x => (harmonicConjugateCircle q x : ℂ)) =
      circleDirichlet (fun x => (q x : ℂ)) := by
  unfold circleDirichlet
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k; simp
  · congr 2
    cases k with
    | ofNat m =>
        cases m with
        | zero => exact (hk rfl).elim
        | succ m =>
            change ‖fourierCoeff (fun x => (harmonicConjugateCircle q x : ℂ)) ((m + 1 : ℕ) : ℤ)‖ ^ 2 = _
            rw [harmonicConjugateCircle_coeff_pos_norm hb m]
            simp only [Int.ofNat_eq_natCast]
    | negSucc m =>
        change ‖fourierCoeff (fun x => (harmonicConjugateCircle q x : ℂ)) (-((m + 1 : ℕ) : ℤ))‖ ^ 2 = _
        rw [harmonicConjugateCircle_coeff_neg_norm hb m]
        simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one]

end Yau.Blueprint.V03Proof
