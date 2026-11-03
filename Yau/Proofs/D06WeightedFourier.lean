import Yau.Proofs.D06WeightedIntegral
import Yau.Proofs.D06HardyRadialTrace

/-! Weighted Hardy orthogonality is exactly the Fourier coefficient identity
for the boundary Gram matrix, at both positive and negative frequencies. -/

open scoped ComplexConjugate
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyTrace_shift_pow_ae (a : HardySeq r) (n : ℕ) (i : Fin r) :
    (fun t => hardyTraceLp ((hardyShiftLI ^ n) a) i t) =ᵐ[hardyCircleMeasure]
      fun t => fourier (n : ℤ) t * hardyTraceLp a i t := by
  induction n with
  | zero =>
    filter_upwards with t
    simp only [pow_zero, Nat.cast_zero, fourier_zero, one_mul]
    rfl
  | succ n ih =>
    rw [pow_succ']
    have h := hardyTrace_shift_ae ((hardyShiftLI ^ n) a) i
    filter_upwards [h, ih] with t ht hi
    change hardyTraceLp (hardyShift ((hardyShiftLI ^ n) a)) i t = _
    rw [ht, hi, Nat.cast_add, Nat.cast_one, fourier_add]
    ring

theorem hardyWeightedInner_shift_left_fourier
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
    (a b : HardySeq r) (n : ℕ) :
    hardyWeightedInner L ((hardyShiftLI ^ n) a) b =
      fourierCoeff (hardyWeightedPoint L a b) (n : ℤ) := by
  rw [hardyWeightedInner_eq_integral L hL, fourierCoeff]
  apply integral_congr_ae
  have h : ∀ᵐ t ∂hardyCircleMeasure, ∀ i : Fin r,
      hardyTraceLp ((hardyShiftLI ^ n) a) i t = fourier (n : ℤ) t * hardyTraceLp a i t :=
    ae_all_iff.mpr (hardyTrace_shift_pow_ae a n)
  filter_upwards [h] with t ht
  simp only [hardyWeightedPoint, smul_eq_mul, fourier_neg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ht i, star_mul, RCLike.star_def]
  ring

theorem hardyWeightedInner_shift_right_fourier
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
    (a b : HardySeq r) (n : ℕ) :
    hardyWeightedInner L a ((hardyShiftLI ^ n) b) =
      fourierCoeff (hardyWeightedPoint L a b) (-(n : ℤ)) := by
  rw [hardyWeightedInner_eq_integral L hL, fourierCoeff]
  apply integral_congr_ae
  have h : ∀ᵐ t ∂hardyCircleMeasure, ∀ j : Fin r,
      hardyTraceLp ((hardyShiftLI ^ n) b) j t = fourier (n : ℤ) t * hardyTraceLp b j t :=
    ae_all_iff.mpr (hardyTrace_shift_pow_ae b n)
  filter_upwards [h] with t ht
  simp only [hardyWeightedPoint, smul_eq_mul, neg_neg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ht j]
  ring

end Yau.NodeProofs.D06Aux
